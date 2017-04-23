__author__ = 'dc'

from stats import *
from logic_program import Atom


def get_conversion_tuple(exception_in_body, exception_in_head):
    out_list = []
#    print "Splitting "+exception_in_body
    procb = str(exception_in_body).split('(',1)[1].split(')',1)[0].split(',')
    proch = str(exception_in_head).split('(',1)[1].split(')',1)[0].split(',')
    for i in range(len(procb)):
        out_list.append((proch[i], procb[i]))
#        print str(proch[i]) + ',' +  str(procb[i])
    return out_list

def getVarConversionFromTuple(tuplewithconversion, variable):
    for (orig, dest) in tuplewithconversion:
        if str(variable) == str(orig):
            return str(dest)
    return False

def convert_all_from_tuple(tuplewithconversion, body):
    newbody = []
    for literal in body:
        a= Atom(str(literal))
        vars = a.getVariables()
        for v in vars:
            q = getVarConversionFromTuple(tuplewithconversion, v)
            if  q:
                newA = str(a).replace(str(v), str(q))
                a= Atom(newA)
            else:
                newA = str(a).replace(str(v), str(v)+"New")
                a= Atom(newA)
        newbody.append(a)
    return newbody



def printall(x):
    print '--------'
    for i in x:
        print '>' + str(i)
    print '--------'

def puttogetherfiles(filenames, name='tmpfilemerge'):
    buf = ''
    for file in filenames:
        f = open(file, 'r')
        for line in f:
            buf+=line
        f.close()
    f = open(name, 'w')
    f.write(buf)
    return 'tmpfilemerge'


def setOfSolutionstoStrippedList(solutions):
    finallist = []
    for isol in solutions:
        locallist = []
        #these are frozensets of clauses
        for j in isol:
            locallist.append(str(j).replace('\n', '').replace('\t', ''))
        finallist.append(locallist)
    return finallist



class OutputWrapper:

     def __init__(self):
         default = True

class MachineOutputWrapper(OutputWrapper):

    def __int__(self):
        default = True

    def toOut(self, out, type = 'info'):
        if type == 'output':
            print out
#        if type =='finalrule':
#            wrapIn(out)

    def printsolutions(self, solutions):
        for isol in solutions:
            for j in isol:
                print str(j).replace('\n', '').replace('\t', '') 
            
    def printstats(self, stats):
        stats.printall()

class GraphOutputWrapper(OutputWrapper):

    def __int__(self):
        default = True

    def toOut(self, out, type = 'info', size = 1):
        if type == 'graph':
            print out
#        if type =='finalrule':
#            wrapIn(out)

    def printsolutions(self, solutions):
        pass

    def printstats(self, stats):
        pass

class HumanOutputWrapper(OutputWrapper):
    debugflag= False
    
    def __int__(self):
        self.debugflag= False

    def toOut(self, out, type = 'info', size = 1):
        if type == 'info' or (self.debugflag and type=='debug'):
            if size == 1:
                print out
            elif size == 2:
                print '---- {0} ----' .format(out)
            elif size == 3:
                print '\n%%%%%%%% {0} %%%%%%%%' .format(out)
            elif size == 4:
                print '\n################ {0} ################\n' .format(out)
            else:
                print out

        

    def printsolutions(self, solutions, empty_hypothesis, type = 'info'):

        i =0
        n = len(solutions)
        if empty_hypothesis:
            i+=1
            n+=1
            if n > 1:
                print '\n----Solution {0}----\n'.format(str(i))
            
        if not type == 'debug' or self.debugflag:
            for isol in solutions:
                i+=1
                if n > 1:
                    print '\n----Solution {0}----\n'.format(str(i))
                #these are frozensets of clauses
                for j in isol:
                    print j



    def printstats(self, stats):
        stats.printall()



def adhocprocessing(line):
    out = line
    if line.startswith('struc4(d98'):
            print "LINE" + str(line)
    if  '\'' in line and (line.startswith('polar(\'') or  line.startswith('size(\'') or line.startswith('flex(\'') or line.startswith('h_doner(\'') or line.startswith('h_acceptor(\'') or line.startswith('pi_doner(\'') or line.startswith('pi_acceptor(\'') or line.startswith('sigma(\'') or line.startswith('branch(\'') or line.startswith('polarisable(\'') or line.startswith('struc3(') or line.startswith('struc4') or line.startswith('subst(subst')):
        s = line.split('\'')

        out = s[0] + 'q' + s[1].replace('-', 'x').replace('(', '').replace(')', '')+s[2]
    if  '\'' in line and (line.startswith('subst(subst')):
        s = line.split('\'')
#        print str(line)
        out = s[0] + 'q' + s[1].replace('-', 'x').replace('(', '').replace(')', '')+s[2]+'q'+ s[3]+'q'+s[4]
    return out