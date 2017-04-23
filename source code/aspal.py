#!/usr/bin/env python

#Limitations:
# - No output variables in the head for now
# - Types can only have arity one (define intermediate predicates if needed)
# - It get slow with longer varlist (for now only 3 outputs are allowed)

#TODO: Close the rule (no pending outs)
#TODO: Noise with iteration mode, is it supported?
#More:
# - Never define domain variables that only contain upper case letter (e.g. AA, AOU, XAFW). They may generate conflict.

"""
It requires as input a learning file and executes the transformation of the file
and the learning through ASP.
"""

import getopt, sys
import os, subprocess
import copy
import logging
from logic_program import *
from clist import *
from aspal_utils import *
from graph_support import *


DEFAULT_FILE = 'bird.lp'
DEFAULT_STATIC = 's.lp'
LOG_FILENAME = 'tmp/aspal.log'
DEFAULT_ARGS = '  --stats --heuristic=vsids '

filename = ''
arguments = ''
solver=''

#PARAMETERS
max_producers = 10
max_consumers = 10
max_rules = 15
max_conditions = 2
imax_conditions = 1
optimal = False #True => Find only the optimal solution(s) (all + optimal = all the optimal solutions)
all = False #True => Find ALL the solutions
solutions_wanted = 1
machine_output = False  #True => Tries to output something easier to process
noise = False   #True => examples are soft constraints
noiteration = False     #True => The depth grows (used when looking for an optimal solution)
incremental_mode = False    # True => Tries to find a best effort solution by revising incrementally the hypothesis
increment = 2 # Literals that are added at each iteration in the incremental mode
suboptimal = False
graph_mode = False
graph_params = ''

empty_hypothesis = False

#STATS
totalabstractrules=0
totalrunningtime=0
lastiterationrunningtime=0

stats = Stats()
om = HumanOutputWrapper()


#LOGGER SETUP
def ensure_dir(f):
    """f is a filename. If f's directory doesn't exist, it's created.
    """
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

# set up logging to file
def setup_logger():
    ensure_dir(LOG_FILENAME)

    logging.basicConfig(level=logging.DEBUG,
                        format='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                        datefmt='%m-%d %H:%M',
                        filename='tmp/aspal.log',
                        filemode='w')
    # define a Handler which writes INFO messages or higher to the sys.stderr
    console = logging.StreamHandler()


    if machine_output    :
        q = logging.FATAL
    else:
        q = logging.INFO
    console.setLevel(q)
    # set a format which is simpler for console use
    formatter = logging.Formatter('%(message)s\n')
    # tell the handler to use this format
    console.setFormatter(formatter)
    # add the handler to the root logger
    logging.getLogger('').addHandler(console)

setup_logger()


def printTask():
    global max_consumers
    global max_producers
    global max_rules
    global max_conditions
    global optimal
    global all

    if all:
        om.toOut("Mode: 2 (all solutions)")
    elif optimal:
        om.toOut("Mode: 3 (optimal solution)")
    else:
        om.toOut("Mode: 1 (any solution)")
    om.toOut("Max rules: " + str(max_rules))
    om.toOut("Max conditions: " + str(max_conditions))
    om.toOut("Max producers: " + str(max_producers))
    om.toOut("Max consumers: " + str(max_consumers))

def updateTaskStats():
    global max_consumers
    global max_producers
    global max_rules
    global max_conditions
    global optimal
    global all

    stats.checkStatUpdate("max_consumers:" + str(max_consumers), True)
    stats.checkStatUpdate("max_producers:" + str(max_producers), True)
    stats.checkStatUpdate("max_condition:" + str(max_conditions), True)
    stats.checkStatUpdate("max_rules:" + str(max_rules), True)

    stats.checkStatUpdate("optimal:" + str(optimal), True)
    stats.checkStatUpdate("all:" + str(all), True)
    

#FILES
def read(filename, asstring = False):
    """
    Reads filename and returns either a list (asstring = True) or a string.
    """
    if asstring:
        lines = ''
    else:
        lines = []
    try:
        file = open(filename, 'rU')
        for line in file:
            nline = re.sub(r'(?<!not)\s', '', line)
            if asstring:
                lines += nline + '\n'
            else:
                lines.append(nline)
        file.close()
    except IOError:
        print "The file does not exist"
    return lines



#PROGRAM
def cartesianProduct(elements):
    if elements == []:
        return []
    outlist = []
    head = elements[0]
    t = elements[1:]
    restCartesian = cartesianProduct(t)
    for e in head:
        if restCartesian == []:
            outlist.append([e])
        for et in restCartesian:
            liste = [e]
            liste.extend(et)
            outlist.append(liste)
    return outlist

def getConstantComparison(flatatom1, flatatom2, consumer):
    if consumer == False:
        comparison = "<="
    else:
        comparison = "<"
    a = CList(flatatom1.constants)
    b = CList(flatatom2.constants)
    if len(a) > 0 and len(b) > 0:
        return "{0} {2} {1}".format(a.toTypedString('c'), b.toTypedString('c'), comparison)
    return False


def orderSatisfied(rule, newflat, consumer=False):
    newouts = rule.lastconditionouts
    oldouts = rule.totouts
    if consumer == False:
        logging.debug("Checking variable use: totvar=" + str(oldouts) + ", lastvar=" + str(newouts))
        for l in newflat.links:
            if l > oldouts - newouts:
                return True
    q = rule.flattening[-1]
    logging.debug("Checking ordering " + str(q) + " < " + str(newflat))
    if q < newflat:
        return True
    elif q == newflat:
        logging.debug("Exactly same condition, constants?")
        additionalconditions = getConstantComparison(q, newflat, consumer)
        #We cannot compare the constants because they are not ground
        #So we add a condition to the rule
        logging.debug("Additional conditions: " + str(additionalconditions))
        if additionalconditions:
            #If not False return them
            return additionalconditions
        else:
            #They are the same and the constants cannot be ordered (empty)
            return not consumer
    return False


def findBindings(outvars, condition):
    """outvars are typed  ('V', 'type')
    Returns a set of elements [  (['A = B', 'C = O'], [2, 3]), .... ]
    """
    logging.debug('Finding bindings')
    logging.debug("Available variables: " + str(outvars))
    logging.debug("Condition to bind: " + str(condition))
    localbindings = []
    ivars = condition.getTypeVariables('i')
    itypes = condition.getTypeConditionsForVariableType('i')
    
    for i in range(len(ivars)):
        #ways contains all the binding for THIS input variable
        ways = []
        for j in range(len(outvars)):
            logging.debug('now' + str(outvars[j]))
            ovar, otype = outvars[j]
            logging.debug('inputis' + itypes[i] + ivars[i])
            if itypes[i] == otype:
                ways.append(('{0}={1}'.format(ovar, ivars[i]), j+1))
        if len(ways) > 0:
            #localbindings should contain one entry (a list of possible
            #bindings) for each input
            localbindings.append(ways)
        else:
            #if one input has no bindings we fail
            return []

    outbindings = cartesianProduct(localbindings)
    return outbindings


def extendRuleWithCondition(rule, modedec, iter = 0):
    """It returns a set of partial bodies (including the flattening
    that adds up to the current clause) and declarations
    """

    condition = Atom(modedec.schema)
    condition.setVariabiliser(rule.variabiliser)
    condition.variabilise()
    mname = modedec.label


    constantvars = CList(condition.getTypeVariables('c'))
    outputvars = CList(condition.getTypeVariables('o'))
    outputnum = len(outputvars)
    constanttypeconds = CList(condition.getTypeConditionsForVariableTypeComplete('c'), 'empty')
    outputtypeconds = CList(condition.getTypeConditionsForVariableType('o'))
    typeconds = CList(condition.getTypeConditions(), 'empty')
    type = modedec.type

    #Builds the clause
    bindingsandlinklist = findBindings(rule.outvars, condition)
    if bindingsandlinklist == []:
        return []

    outrules = []

    for bindingelement in bindingsandlinklist:
        #A new rule for each binding
        newrule = copy.deepcopy(rule)
        allinks=[]
        for (b, l) in bindingelement:
            newrule.addCondition(b)
            allinks.append(l)
        newflat = Flatatom(mname, constantvars, allinks)
        if type == 'p':
            orderSat = orderSatisfied(rule, newflat)
        elif iter > 1:
            orderSat = orderSatisfied(rule, newflat, consumer=True)
        else:
            orderSat = True
        if not orderSat == False:
            newrule.addConditions(typeconds)
            newrule.addCondition(str(condition))
            for i in range(len(outputvars)):
                newrule.addOutputVariable((outputvars[i], outputtypeconds[i]))
            newrule.addFlattening(newflat, constantFlattening=constanttypeconds)
            newrule.totouts +=outputnum
            newrule.lastconditionouts = outputnum
            if isinstance(orderSat, str):
                newrule.addConstraint(orderSat)
            outrules.append(newrule)

    return outrules


def growConsumer(rule, modedec):
    outrules = []
    outrules.append(rule)
    logging.debug('#Adding consumer {0}'.format(modedec))
    logging.debug('#Flattening of the rule')
    for f in rule.flattening:
        logging.debug('#'+str(f))
    max_mode = None
    if modedec.getOption('max'):
        max_mode = int(str(modedec.getOption('max')))
    consumerlength = len(rule.flattening) - rule.producerlength
    rule_length = len(rule.flattening)
    logging.debug('#Consumer length ' + str(consumerlength))
    iter = 1
    if not max_mode:
        max_mode = max_consumers
    #We do as many iteration as the instances of the modedec we can add
    newRules = [rule]
    while consumerlength < max_consumers and iter <= max_mode and rule_length <= imax_conditions:
        #In onw instance we get all the rules that we have (one in the first iteration)
        #In each of these iteration we act on the last produced set
        logging.debug('##Iteration ' + str(iter))
        nextRules=[]
        for r in newRules:
            logging.debug('###Extending ' + str(r))
            copyrule = copy.deepcopy(r)
            here = extendRuleWithCondition(copyrule, modedec, iter=iter)
            nextRules.extend(here)
            logging.debug('###Got {0} new rules'.format(len(here)))
            #Note that we keep the old rule
        logging.debug('##Got a total of {0} new rules:'.format(len(nextRules)))
        for r in nextRules:
            logging.debug(r)
        outrules.extend(nextRules)
        newRules = nextRules
        iter+=1
        consumerlength+=1
        rule_length+=1
    return outrules

    
def grow(rule, modedecs):
    outrules = []
    outrules.append(rule)
#    consumernew = growConsumers(rule, modedecs)
#    outrules.extend(consumernew)
    logging.debug('Flattening of the rule')
    for f in rule.flattening:
        logging.debug(str(f))
    if len(rule.flattening) <= max_producers and len(rule.flattening) <= imax_conditions:
        for m in modedecs:
            if m.type == 'p':
                max_mode = False
                if m.getOption('max'):
                    max_mode = int(str(m.getOption('max')))
#                copiedrule = copy.deepcopy(rule)
                pcount = 0
                for q in rule.flattening:
                    if q.mode == m.label:
                        pcount+=1

                logging.debug("Evaluating extension with " + str(m))
                newrules = []
                if (max_mode and max_mode) < 1 or not max_mode or (max_mode and pcount < max_mode):
                    newrules = extendRuleWithCondition(rule, m)
                logging.debug("Extended in {0} new rules".format(str(len(newrules))))
                if newrules != []:
                    for rulen in newrules:
                        logging.debug(rulen)
                        addrules = grow(rulen, modedecs)
                        outrules.extend(addrules)
    return outrules



def makeHead(modedec, variabiliser):
    """It returns a list of clauses of strings that go
    into the final top theory
    """

    #Gathers variables and typechecks
    head = Atom(modedec.schema)
    head.setVariabiliser(variabiliser)
    head.variabilise()
    mname = modedec.label

    logging.debug('Anything in here? ' + str(head))

    constantvars = CList(head.getTypeVariables('c'))
    constanttypeconds = CList(head.getTypeConditionsForVariableTypeComplete('c'))
    inputvars = CList(head.getTypeVariables('i'))
    inputnum = len(inputvars)
    inputtypeconds = CList(head.getTypeConditionsForVariableType('i'))
    #    constanttypeconds = CList(head.getTypeConditionsForVariableTypeComplete('c'), 'empty')
    typeconds = CList(head.getTypeConditions(), 'empty')

    #Builds the clause
    returned_clause = Clause(head = str(head), body = [], variabiliser = variabiliser)
    returned_clause.addFlattening(Flatatom(mname, constantvars), constantFlattening=constanttypeconds)
    returned_clause.addConditions(typeconds)
    returned_clause.totouts =inputnum
    returned_clause.lastconditionouts = inputnum

    for i in range(inputnum):
        returned_clause.addOutputVariable((inputvars[i], inputtypeconds[i]))

    #    declarations = [declaration1, declaration2, declaration3, declaration4, returned_clause]
    declarations = []
    return returned_clause, declarations


def typingformat(cnstlist):
    if cnstlist == []:
        return ''
    out = ":"
    for c in cnstlist:
        out+=c+":"
    return out[0:-1]


def createTop(modedecs):
    global noise
    rules = []
    finalrules = []
    modedecs.sort()
    for mode in modedecs:
        if mode.type == 'h':
            vrb = Variabiliser()
            logging.debug('Making head for modedec: ' + str(mode))
            top, _ = makeHead(mode, vrb)
#            declarations.extend(declaration)
            logging.debug('Head ready: ' + str(top) + ' with flattenig ' + str(top.flattening))
            rules.append(top)
    logging.debug('Head processed, now expanding the rules')
    for rule in rules:
        #Careful, do not modify the original rule but make a copy
        logging.debug('Extending rule: ' + str(rule))
        alltherules = grow(rule, modedecs)
        finalrules.extend(alltherules)
    for m in modedecs:
        if m.type == 'c':
            #DEBUG
            logging.debug(">>>Now considering mode " + str(m))
            logging.debug(">>>On the following rules ")
            for r in finalrules:
                logging.debug(r.toLineStr())

            newrules = []
            for rule in finalrules:
                #finalrules.remove(rule)
                logging.debug("Processing" + rule.toLineStr())
                if rule.producerlength is None:
                    rule.producerlength =len(rule.flattening)
                newm = growConsumer(rule, m)
                newrules.extend(newm)

            #DEBUG
            logging.debug(">>>Now the new rules are ")
            for r in newrules:
                logging.debug(r.toLineStr())

            finalrules = newrules

    bigstringofabducibles = ''
    bigstringofoptimisation = ''
    stuffornoise= ''
    for rule in finalrules:
        abd = rule.getAbd()
        rule.addCondition(abd)
        tf = typingformat(rule.constantflattening)
        constrs = typingformat(rule.constraints)
        bigstringofabducibles += abd+tf+constrs+','
        if str(rule.head).startswith("exception"):
            subtract = 1 #TODO: now they are normal rules. We can treat exceptions differently
        else:
            subtract = 0
        if optimal:
            lastpart = '='+str(len(rule.flattening) - subtract)+','
            bigstringofoptimisation +=abd+tf
            bigstringofoptimisation+=lastpart
        if noise:
            lastpart = '='+str(len(rule.flattening)- subtract)+','
            stuffornoise+=abd+tf
            stuffornoise+=lastpart

    bigstringofabducibles="0 {"+bigstringofabducibles[0:-1]+"} " + str(max_rules) + "."
    if optimal:
            bigstringofoptimisation = "#minimize ["+bigstringofoptimisation[0:-1]+"].\n"
#    print bigstringofoptimisation
    return finalrules, bigstringofabducibles, bigstringofoptimisation, stuffornoise



def createModeDecs(modedecs):
    q = []
    for line in modedecs:
        m = ModeDeclaration(line)
        q.append(m)
    return q


def parseFile(filename, additional_theory = ''):
    """Given a path to a file, it returns a list
    [modedecs, options, examples, goal, background].
    The list contains trimmed lines from the file
    (no syntax check).
    """
    modedecs=[]
    options=[]
    examples=[]
    goal=[]
    background=""
    filetext = read(filename)
    for line in filetext:
        line = adhocprocessing(line)
        if line.startswith("mode") :
            modedecs.append(line)
        elif line.replace(' ','').startswith(":-mode") :
            modedecs.append(line.replace(':-', ''))
        elif line.startswith("example("):
            examples.append(line)
        elif line.startswith("option("):
            options.append(line)
        elif line.startswith("goal("):
            goal.append(line)
        elif not line.startswith("%"):
            background = background + line + '\n'
            
    additional_theory = additional_theory.split('\n')
    for line in additional_theory:
        if line.startswith("mode") :
            modedecs.append(line)
        elif line.startswith("example("):
            examples.append(line)
        elif line.startswith("option("):
            options.append(line)
        elif line.startswith("goal("):
            goal.append(line)
        elif not line.startswith("%"):
            background = background + line + '\n'
    return [modedecs, options, examples, goal, background]


def makegoal(goal, examples = '', stuffornoise=''):
    global noise
    global incremental_mode
    npos = 0
    nneg = 0
    #TODO: support this with an option
    if incremental_mode:
        multiplier = 1
    else:
        multiplier = 1
    if goal and not noise:
        return ':- not ' + str(Atom(goal[0]).arguments[0]) + '.\n', 1, 0
    elif not goal and not noise:
        s1 = ''
        for i in examples:
            a = Atom(i)
            
            pos =  int(str(a.arguments[1]))
            if pos > 0:
                npos += 1
                s1+= str(a.arguments[0])+','
            else:
                nneg +=1
                s1+= 'not '+str(a.arguments[0])+','
        return ':- not goal_made_from_examples. \n goal_made_from_examples :- {0}.\n'.format(s1[0:-1]), npos, nneg
    else:
        #Noise case only optimisation
        s1 = ''
        value = multiplier * 1
        for i in examples:
            a = Atom(i)
            pos =  int(str(a.arguments[1]))
            if pos > 0:
                npos +=1
                s1+= str(a.arguments[0])+'=-{0},'.format(str(value))
            else:
                nneg +=1
                s1+= str(a.arguments[0])+'={0},'.format(str(value))
        return '#minimize [{0},{1}].\n'.format(s1[0:-1],stuffornoise[0:-1]), npos, nneg


def staticTop():
    out = read(DEFAULT_STATIC, True)
    return out


def process_file(filename, additional_theory=''):
    #Splits lines
    [modedecs, _, examples, goal, background] = parseFile(filename, additional_theory)
    logging.debug('File parsed successfully')
    #Creates mode declarations (with type and label)
    fullmodedecs = createModeDecs(modedecs)
    logging.debug('Starting creation of the top theory')
    top, abducibledec, optdec, stuffornoise = createTop(fullmodedecs)
    stats.checkStatUpdate('total_skeleton_rules:'+str(len(top)))

    om.toOut('Top theory created', type='debug')
    goalic, npos, nneg = makegoal(goal, examples, stuffornoise)

    #optionout = makeoptions(options)
    om.toOut('Goal and options processed', type='debug')
    static = staticTop()

    finalfile = ''
    if optimal and not noise:
        finalfile+=optdec

    #goalic must be after abducibledec!
    finalfile+=abducibledec+background+static+goalic

    for r in top:
#        print r.toLineStr()
#        print str(r)
        finalfile+=str(r)

    tempfilename = 'tmp/' + filename.split('.')[0] + '_workfile'
    ensure_dir(tempfilename)
    f=open(tempfilename, 'w')
    f.write(finalfile)
    f.close()
    logging.debug('Temporary file created in %s' % tempfilename)
    return tempfilename, fullmodedecs, npos, nneg


def getElementsNoEmpty(atom):
    if len(atom.arguments)  > 0:
        return atom.arguments
    else:
        return []


def transform_rule(r, modedecs):
    outputlist = []
    #r is of the type rule(l((h0,const(empty),links(empty)),(b2,const(empty),links(2))),  (0,  (bx0,const(empty),links(1)), 0))

    lmodedecs = dict()
    for m in modedecs:
        lmodedecs[m.label] = m

    q = Atom(r)
    rest = q.arguments[0] #(0,  (bx0,const(empty),links(1)), 0)
    flattenedlist = rest.arguments

    bodyargs = flattenedlist[1:]
    headarg = flattenedlist[0]

    allvars = Variabiliser()
    #HEAD

    i = headarg.arguments[0]
    modename = i.predicate
    constants = getElementsNoEmpty(headarg.arguments[1])
    headschema = Atom(lmodedecs[str(modename)].schema)
    clistins = allvars.getNewVariables(headschema.countPlacemarkers('+'))
    clistouts = allvars.getNewVariables(headschema.countPlacemarkers('-'))
    headschema.changeInputsFromList([clistins, clistouts, constants], [range(1, len(clistins)+1), range(1, len(clistouts)+1), range(1, len(constants)+1)])
    vatom = headschema
    outputlist.extend(vatom.getTypeVariables('i'))
    outclause = Clause(vatom, [])
    outclause.addFlattening(headarg)
    outclause.outvars.extend(clistins)
    outclause.outvarstypes.extend(headschema.getTypeConditionsForVariableType('i'))
    outclause.addConditions(vatom.getTypeConditionsForVariableTypeComplete('i'))
    outclause.addConditions(vatom.getTypeConditionsForVariableTypeComplete('o'))
    #outclauselist.extend(types) #these are string
    #BODY
    for i in bodyargs:
        modename = i.arguments[0].predicate
        schema = Atom(lmodedecs[str(modename)].schema)
        constants = getElementsNoEmpty(i.arguments[1])
        links = getElementsNoEmpty(i.arguments[2])
        clistouts = allvars.getNewVariables(schema.countPlacemarkers('-'))
        schema.changeInputsFromList([outputlist, clistouts, constants], [links, range(1, len(clistouts)+1), range(1, len(constants)+1)])
        vatom = schema
        outputlist.extend(vatom.getTypeVariables('o'))
        outclause.addCondition(vatom)
        outclause.addFlattening(i)
        outclause.outvars.extend(clistouts)
        outclause.outvarstypes.extend(schema.getTypeConditionsForVariableType('o'))
        outclause.addConditions(vatom.getTypeConditionsForVariableTypeComplete('i'))
        outclause.addConditions(vatom.getTypeConditionsForVariableTypeComplete('o'))
    return outclause

def printrunningoptions():
    global max_rules
    global max_conditions
    global imax_conditions
    global noise

    om.toOut('\tCurrent execution parameters')
    om.toOut('\t\tnoise={0}'.format(str(noise)))
    om.toOut('\t\tmax_rules={0}'.format(str(max_rules)))
    om.toOut('\t\tmax_conditions={0}'.format(str(imax_conditions)))
    om.toOut('\t\t(condition limit)={0}'.format(str(max_conditions)))

def aspExecute(filename, solver, modedecs):
    """
    solutions return all the solutions in this execution (just all the solutions we encounter)
    bestsolutions returns all the best solutions (lowest complexity or lowest noise + lowest complexity)
    bestscore returns the complexity of the best solution (or in case of noise the tuple score)
    """
    global om
    global noise
    global stats
    global arguments
    global empty_hypothesis

#    om.toOut("Execution line: " +solver+' '+filename)
    proc = subprocess.Popen(solver+' < '+filename, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    printrunningoptions()
    feedbackstate = None
    solutions = set()
    bestscore = None
    bestsolution = set()
    currentsolution = set()

    
    for line in iter(proc.stdout.readline,''):
        #Just debug the line as it is
        logging.debug(line)
        if (line.startswith('Optimization:') or line.startswith('  Optimum   :') or line.startswith('Time        :') or line.startswith('  Prepare   ')\
        or line.startswith('  Prepro.   :') or line.startswith('  Solving   :') or line.startswith('UNSATISFIABLE') or feedbackstate == 'stats') and not machine_output:
            #Just show it
            if (not stats.checkStatUpdate(line)):
                om.toOut(line.rstrip(), type='debug')


        if line.startswith('SATISFIABLE') or line.startswith('OPTIMUM'):
            feedbackstate = 'stats'

        if line.startswith('ERROR') or feedbackstate == 'error':
            logging.error(line)
            feedbackstate = 'error'

        if line.startswith('% warning'):
            om.toOut(line)



        if line.startswith('rule') or feedbackstate == 'answer':
            #In this case we have a hypothesis
            feedbackstate = 'None'
            if len(line.strip()) == 0:
                empty_hypothesis = True
            else:
                rules = line.rstrip().split(' ')
                totalliterals = 0
                for r in rules:
                    print r
                    currentclause = transform_rule(r, modedecs)
                    totalliterals += currentclause.getComplexity()
                    currentsolution.add(currentclause)
                    om.toOut(str(currentclause))
            #We add the solution to solutions anyway

                if noise:
                    line = proc.stdout.readline()
                    om.toOut(line)
#                    print "I'm reading a new line " + line
                    sl = line.split(' ')
                    score = sl[1]
                    newscore = score
                else:
                    newscore = totalliterals

                om.toOut('==================\n')
#                print 'Newscore = ' + newscore
                solutions.add(frozenset(currentsolution))
                if bestscore is None or int(bestscore) > int(newscore):
                    om.toOut('Bestscore=' + str(newscore))
                    bestscore = newscore
                    bestsolution.clear()
                    bestsolution.add(frozenset(currentsolution))
                elif newscore == bestscore:
                    bestsolution.add(frozenset(currentsolution))



        if line.startswith('Answer:') or line.startswith('Brave consequences:'):
            feedbackstate = 'answer'
            om.toOut('\n==================\n\nNew answer found: #'+line.split(':')[1])
            currentsolution = set()
      
    return solutions, bestsolution, bestscore

def execute_i(filename, solver, arguments, additional_theory=''):
    global om

    tempfile, modedecs, npos, nneg = process_file(filename, additional_theory)
#    om.toOut('Successfully processed %s. Now starting the solver' % \
#             (filename))
#    om.toOut('Invoking %s %s' % (solver, arguments))
    solutionshere, bestsolutionhere, complexityhere = aspExecute(tempfile, solver+' '+arguments, modedecs)
    return solutionshere, bestsolutionhere, complexityhere, npos, nneg


def start_iteration(additional_theory = ''):
    global max_consumers
    global max_producers
    global max_rules
    global imax_conditions
    global max_conditions
    global optimal
    global all
    global om
    global stats
    global arguments
    global filename
    global solver
    global noiteration
    global suboptimal

    stats.startTime()
    #Processing file

    #In this case there is no iteration
    if (all and not suboptimal) or noiteration:
        om.toOut('Running in no-iteration mode', size=2)
        imax_conditions = max_conditions
        solutionshere, bestsolutionhere, complexityhere, npos, nneg = execute_i(filename, solver, arguments, additional_theory)
        solutions= solutionshere
        stats.stopTime()
        return solutions, bestsolutionhere, complexityhere
    else:
        om.toOut('Running in iteration mode', size=2)
        #Initial case, not conditions
        imax_conditions = 0
        #Empty set of solutions
        solutions = set()
        bestsolution = set()
        score = None
        hasbeensatisfiable = False
        satisfiablenow = False
        #SCORE: LOWER IS BETTER

        while True:
            om.toOut("Starting a new iteration", type='info')
            solutionshere, bestsolutionhere, scorehere, npos, nneg = execute_i(filename, solver, arguments, additional_theory)
            if len(solutionshere) > 0:
                satisfiablenow = True
                hasbeensatisfiable = True
            else:
                satisfiablenow = False
            om.toOut("Score in the last iteration={0}\n Best score={1}".format(str(scorehere), str(score)))
            if (score is None and scorehere ) or (score and scorehere and int(score) > int(scorehere)):
                bestsolution = bestsolutionhere
                score = int(scorehere)
            elif (score and scorehere and int(score) == int(scorehere)):
                #Found solutions with same complexity, adding to old ones
                bestsolution.union(bestsolutionhere)
            solutions.union(solutionshere)
            if imax_conditions == 0:
                imax_conditions = 1
            else:
                if suboptimal:
                    imax_conditions += 1
                else:
                    imax_conditions = imax_conditions * 2

            #What is the best solution we can find that wasn't found before?
            #max coditions and single rule
            #Remember it's all negated. The higher the better

                #Upper bound next: the next iteration must produce something lower or equal
                #This is given to the opt-value parameter


            if imax_conditions > max_conditions or (not satisfiablenow and hasbeensatisfiable): # or ((not score is None ) and upper_bound_next >= score):
                break


            if scorehere:
                if suboptimal:
                    break
                    
                upper_bound_next = int(score) - 1

                om.toOut("Lower bound next " + str(upper_bound_next), type='info')
                om.toOut("Current score " + str(score), type='info')
                if re.search('--opt-value=[0-9]+', arguments):
                    arguments = re.sub('--opt-value=[0-9]+', '--opt-value='+str(upper_bound_next), arguments)

        #Now we have a final result
        om.toOut("\n____Best solutions found with score {0}____".format(str(score)), type='info')
        #print bestsolution
        for i in bestsolution:
            om.toOut("____Solution____\n", type='info')
            for j in i:
                om.toOut(str(j))

        stats.stopTime()
        if not optimal:
            l = len(solutions)
        else:
            l = len(bestsolution)
        #changed so that solutions=1 in case of an empty solution    
        if int(l) > 0:
            stats.allstats['solutions'] = int(l)
        else:
            stats.allstats['solutions'] = stats.allstats['models']   
        return solutions, bestsolution, score

def manage_output(solutions, bestsolution, complexity):
    global stats
    global all
    global incremental_mode
    global empty_hypothesis
    #stats.printall()

    if all and not incremental_mode and not optimal:
        l = solutions
    else:
        l = bestsolution

    om.toOut("\n\n\n\n\n\n####################################\nStatistics\n####################################\n\n")
    om.printstats(stats)
    if stats.allstats['models'] > 0:
        om.toOut("\n\n\n####################################\nFinal output\n####################################\n\n")
        om.printsolutions(l,empty_hypothesis)
        #a = json.dumps({'solutions' : l}, separators=(',',':'))

def usage():
    print "Sorry, not currently implemented"


def setgraphiterationparam(key, i):
    global max_conditions
    global max_consumers
    global max_rules
    global max_producers

    if key == 'max_conditions':
        max_conditions = i
    elif key == 'max_rules':
        max_rules = i
    elif key == 'max_producers':
        max_producers = i
    elif key == 'max_consumes':
        max_consumers = i



def makeexceptions(sol):
    allmodes = []
    allnewrules = []

    for  r in sol:
#        print str(r.printAllInfo())
        id = ''
        for i in r.flattening:
            id+='({0}),'.format(i)
        excout= ''
        for i in r.outvars:
            excout+='{0},'.format(i)
        typestr = ''
        for i in r.outvarstypes:
            typestr+='+{0},'.format(i)
        newcond = "exception(id({0}), v({1}))".format(id[0:-1].replace('(','').replace(')','').replace(',',''), excout[0:-1]).replace('-', 'minus')
        newmode = ModeDeclaration("modeh(exception(id({0}), v({1})))".format(id[0:-1].replace('(','').replace(')','').replace(',',''), typestr[0:-1]).replace('-', 'minus'))
#        print newmode
        allmodes.append(newmode)
        newrule = copy.deepcopy(r)
        newrule.addCondition(newcond)
        allnewrules.append(newrule)
    return allnewrules, allmodes


def refactor_revision(currentrules, sol):
    finalrules = []
    for original in currentrules:
        for new in sol:
            if str(new.head).startswith("exception"):
                for literal in original.body:

                    aliteral = Atom(str(literal))

                    ahead = Atom(str(new.head))
                    if len(aliteral.arguments) > 0 and len(ahead.arguments) > 0:
    #                    print "Trying to match {0} and {1}".format(aliteral.arguments[0], ahead.arguments[0])
                        if str(aliteral.arguments[0]) == str(ahead.arguments[0]):
                            tuplewithconversion = get_conversion_tuple(str(aliteral.arguments[1]), str(ahead.arguments[1]))
                            convertedconds = convert_all_from_tuple(tuplewithconversion, new.body)
#                            print 'Lite ' + str(aliteral)
                            modrule = copy.deepcopy(original)
                            modrule.body = modrule.body[0:-1]
#                            printall(convertedconds)
                            modrule.addConditions(convertedconds)
#                            print modrule
                            finalrules.append(modrule)
            else:
                finalrules.append(new)
    return finalrules


def printincrementalcurrentbestsolution(rbestsolution, newrules, additional = ''):
    om.toOut("\n\n========================================\n")
    om.toOut('Current best solution:\n')
    om.printsolutions([rbestsolution])
    om.toOut('New rules for revision:\n', type='debug')
    om.printsolutions([newrules], type='debug')
    om.toOut(additional)
    om.toOut("========================================\n\n\n")

def incremental():
    '''
    EXPERIMENTAL
    The idea is we use a depth increment to derive a set of rules.
    Then we enrich that set of rules using exceptions and so on...
    '''
    global max_conditions
    global max_consumers
    global max_producers
    global all
    global arguments
    global noiteration
    global noise
    global optimal
    global increment



    #Run the initial step
    max_producers = increment
    max_consumers = increment
    max_conditions = increment - 1
    all = True
    #We don't do the iteration but
    #we want the optimal solution
    om.toOut("increment={0}".format(str(increment)))
    optimal = True
    noise = True
    #We don't want to iterate
    noiteration = False

    #First iteration, we can start as usual since we don't have exceptions
    _, bestsolution, score = start_iteration()
    oldcurrentrules = bestsolution
    
    if len(bestsolution):
        rbestsolution = bestsolution.pop()
        newrules, modeexceptions = makeexceptions(rbestsolution)

        additionalt = ''
        for i in newrules:
            additionalt += str(i)+'\n'

        for i in modeexceptions:
            additionalt += str(i)+'\n'
    else:
        om.toOut("\n\nNo solution at the first stage: terminating")
        return

    upper_bound_next = int(score) - 1

    if re.search('--opt-value=[0-9]+', arguments):
        arguments = re.sub('--opt-value=[0-9]+', '--opt-value='+str(upper_bound_next), arguments)
    else:
        arguments +=  ' --opt-value='+str(upper_bound_next)


    currentrules = newrules
    printincrementalcurrentbestsolution(rbestsolution, newrules)


    while True:
        om.toOut("\n>>>>>>>>>>>>> Starting a new incremental step search to improve the current solution\n")
        oldscore = score
        _, bestsolution, score = start_iteration(additionalt)

        if not bestsolution:
            score = oldscore
            currentrules = oldcurrentrules
            break

        rbestsolution = bestsolution.pop()
        om.toOut("New solution: ", type='debug')
        om.printsolutions([rbestsolution], type='debug')

        om.toOut("Before refactoring: ", type='debug')
        om.printsolutions([currentrules], type='debug')

        currentrules = refactor_revision(currentrules, rbestsolution)


#        om.toOut("After refactoring: ")
#        om.printsolutions([currentrules])
        currentrulesforprint = currentrules


        if int(score) >= int(oldscore):
            score=oldscore
            om.toOut("Stopping")
            break
            

        oldcurrentrules = currentrules

        currentrules, modeexceptions = makeexceptions(currentrules)

        printincrementalcurrentbestsolution(currentrulesforprint, currentrules, "\nNew score: {0}, Old score {1}\n".format(str(score), str(oldscore)))

        additionalt = ''

        for i in currentrules:
            additionalt += str(i)+'\n'

        for i in modeexceptions:
            additionalt += str(i)+'\n'

        max_conditions = increment

        upper_bound_next = score 


#    om.toOut("#### Final solution ####")
#    om.printsolutions([currentrules])

    return [currentrules], [currentrules], score







def executegraph(a):
    global filename
    global arguments
    global om
    global solver
    global stats

    targets= []
    ALLOWED_SETTINGS = ['max_conditions', 'max_rules', 'max_consumers', 'max_producers']

    parameters = a.split(';')
    if len(a) < 2:
        print "Please provide at least a target value and an iteration value e.g. total_time;max_conditions[0,10]"
        return
    om.toOut("Target value " + parameters[0])

    for i in parameters:
        if not '[' in i:
            targets.append(i)
    arglist = [targets]
    for i in parameters:
        if '[' in i:
            q = i.split('[')
            if len(q) < 2:
                print "\tPlease provide iteration values"
                return
            key = q[0]
            values = q[1].split(']')[0]
            if key in ALLOWED_SETTINGS:
                om.toOut("Iteration value " + key)
                om.toOut("\t on values " + values)
                #valueson[key] = values
                arglist.extend([key, values])
            else:
                print "Iteration value {0} not allowed".format(i)
    for i in arglist:
        print i
    if len(arglist) == 3:
        ag = AspalGraph(arglist[0], arglist[1], arglist[2])
    elif len(arglist) == 5:
        ag = AspalGraph(arglist[0], arglist[1], arglist[2], arglist[3], arglist[4])
    else:
        print "Error with the inputs"


    for i in ag.i1range :
        om.toOut('Now executing with {0} set to {1}'.format(ag.i1, str(i)), 'graph')
        setgraphiterationparam(ag.i1, i)
        for j in ag.i2range :
            om.toOut('Now executing with {0} set to {1}'.format(ag.i2, str(j)), 'graph')
            setgraphiterationparam(ag.i2, j)

            checkParametersAndExecute()

            tmp = [i, j]
            for t in targets:
                tmp.append(stats.allstats[t])
            ag.points.append(tmp)

    print ag
    print

    savedstring = ''
    om.toOut(ag.csvheader(), 'graph')
    savedstring += ag.csvheader() + '\n'
    for i in ag.points:
        s = ''
        for j in i:
            s+= str(j)+','
        om.toOut(s[:-1], 'graph')
        savedstring += s[:-1] + '\n'
    ag.makeGraph()

    
    if ('max_rules' == ag.i1 or 'max_rules' == ag.i2) and ('max_conditions' == ag.i1 or 'max_conditions' == ag.i2):
        out2 = rearrangeAttributes(savedstring, 'max_rules', ag.targets[0], 'max_conditions')
        f = open('tmp/rc.csv', 'w')
        f.write(out2)
        f.close()


def checkParametersAndExecute():
    global graph_mode
    global graph_params


    #Initialise stats
    stats = Stats()
    om.toOut('Executing ASPAL on file %s using solver %s.\nDebug logs in %s' % \
                     (filename, solver, LOG_FILENAME), type='info')
    printTask()
    updateTaskStats()
    if incremental_mode:
        om.toOut("Running incrementally", size = 3)
        solutions, bestsolution, score = incremental()
    else:
        #Core
        solutions, bestsolution, score = start_iteration()
        #Finalise
    manage_output(solutions, bestsolution, score)
#    if noise:
#        "Be careful, check that the --opt-value= function is updated correctly with respect to the optimisation of the examples. THIS IS STILL NOT IMPLEMENTED."


def main():
    '''
    Supported modes
    -n: Allows noisy examples. It works with -o (it iterates on the depth)
    -o: iterates on the  depth
    -i x: incremental (includes the -n). The depth increment is x
    default: finds all solutions
    --solutions x: finds x solutions
    '''
    global DEFAULT_ARGS
    global DEFAULT_FILE

    global max_consumers
    global max_producers
    global max_rules
    global imax_conditions
    global max_conditions
    global optimal
    global all
    global silent
    global machine_output
    global filename
    global arguments
    global om
    global solver
    global noise
    global incremental_mode
    global increment
    global noiteration
    global graph_mode
    global graph_params
    global solutions_wanted
    global suboptimal

    #Checking the inputs
    try:
        opts, args = getopt.getopt(
            sys.argv[1:],
            "f:hs:ap:c:r:m:oz:ni:l",
            ["help",
             "subopt",
             "all",
             "alloptimal",
             "max_consumers=",
             "max_producers=",
             "max_rules=",
             "max_conditions=",
             "optimal",
             "machine",
             "graph=",
             "noise",
             "timelimit=",
             "solutions=",
             "incremental=",
             "extradebug"])
    except getopt.GetoptError, err:
        # print help information and exit:
        print str(err)
        # will print something like "option -a not recognized"
        usage()
        sys.exit(2)
    #Default options
    solver= './clingo'
    arguments= DEFAULT_ARGS
    filename= DEFAULT_FILE
    graphmode=False
    for o, a in opts:
        if o in ("-h", "--help"):
            usage()
            sys.exit()
        elif o in ("-z"):
            #Give other arguments in a string "--heuristic=..."
            arguments += ' ' + a + ' '
        elif o in ("--timelimit"):
            arguments += ' --time-limit=' + a + ' '
        elif o in ("-f"):
            if not ',' in a:
                filename = a
            else:
                filenames = a.split(',')
                om.toOut("Files:")
                for q in filenames:
                    om.toOut(q)
                tempname = puttogetherfiles(filenames)
                filename = tempname
        elif o in ("-i", "--incremental"):
            noise = True
            incremental_mode = True
            increment = int(a)
        elif o in ("-s", "--solver"):
            solver = a
        elif o in ("-m", "--max_conditions"):
            max_conditions = int(a)
        elif o in ("-p", "--max_producers"):
            max_producers = int(a)
        elif o in ("-c", "--max_consumers"):
            max_consumers = int(a)
        elif o in ("-r", "--max_rules"):
            max_rules = int(a)
        elif o in ("-a", "--all"):
            all = True
        elif o in ("--solutions"):
            solutions_wanted = a
        elif o in ("--subopt"):
            suboptimal = True
        elif o in ("-o", "--optimal"):
            optimal = True
        elif o in ("-l"):
            arguments += ' --search-limit=100000,100000 '
        elif o in ("-n", "--noise"):
            noise = True
            noiteration = True
        elif o in ("--machine"):
            om = MachineOutputWrapper()
        elif o in ("--extradebug"):
            om.debugflag = True
        elif o in ("--graph"):
            graph_mode=True
            #Example
            #--graph='total_time;max_conditions[1:4];max_rules[1:10]'
            graph_params = a
            om = GraphOutputWrapper()
        else:
            assert False, "unhandled option"

    if not optimal:
        all = True

    # arguments changed
    
    if optimal:
        arguments = '--stats --heuristic=vsids  --opt-all --opt-heu'
    else:
        arguments = '--stats --heuristic=vsids  0'

    #EXECUTION
    #Execution
    if graph_mode:
        om.toOut("Graph mode", size=3)
        executegraph(graph_params)
        return
    else:
        checkParametersAndExecute()

if __name__ == "__main__":
    main()
  
