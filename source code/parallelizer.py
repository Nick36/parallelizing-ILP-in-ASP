import sys, os, re, itertools, traceback, networkx as nx
from multiprocessing import Process, Queue
from subprocess import check_output

# PART 1 function definitions

# input: a file to exectute in ASPAL
# output: a set of rules corresponding to different solutions
def get_rules(filename):
    rules = set()
    if sys.argv[1] == '--optimal':
        output = check_output(['./aspal.py', '-of', filename])
    else:
        output = check_output(['./aspal.py', '-f', filename])

    if "\n\n\n####################################\nFinal output\n####################################\n\n" not in output:
        print "No solutions."
        return set(['no_solution'])

    output = output.split("\n\n\n####################################\nFinal output\n####################################\n\n")[1]
    if '----' in output:
        separators = []
        lines_output = output.splitlines()
        for i,l in enumerate(lines_output):
            if l.startswith('----'):
                separators.append(i+1)
        # append last line index + 1
        separators.append(i+1)
        for i in xrange(len(separators)-1):
            start_line = separators[i]
            end_line = separators[i+1] - 1
            r = re.sub(r'\.','.\n',re.sub(r'(?<!not)\s','',''.join(lines_output[start_line:end_line])))
            rules.add(r)
    else:
        rules.add(re.sub(r'\.','.\n',re.sub(r'(?<!not)\s','',''.join(output))))

    #print rules, filename
    return rules

# input: filename to exectute, head predicates it corresponds to, a string of rules for the defining predicates of that head predicates
# output: a set of strings, each string containing rules computed by ASPAL for the given head predicate according to the subprogram specified in filename
def run_subtask(filename, predicates, rules):
    try:
        fwrite = open(filename,"w")
        for p in predicates:
            for h in head_indizes[p]:
                fwrite.write(lines[h]+"\n")
            if p in example_indizes:
                for i in example_indizes[p]:
                    fwrite.write(lines[i]+"\n")
        for i in line_indizes:
            fwrite.write(lines[i]+"\n")
        fwrite.write(rules)
        fwrite.close()
        subtask_rules = get_rules(filename)
        # delete temporary file
        os.remove(filename)
        return subtask_rules
    except:
        print "Unexpected error:"
        exc_type, exc_value, exc_traceback = sys.exc_info()
        exc_lines = traceback.format_exception(exc_type, exc_value, exc_traceback)
        print ''.join('!! ' + line for line in exc_lines)

# input: a node of the dependency graph, a string of defining rules of its predecessors, index among all files for that node,
#        a queue to store output (shared between all separate processes for the components and main process)
# output into the queue: a set of strings, each string containing some local rules (part of a hypothesis) for the node
def compute_rules(node, defining_rules_of_predecessors, k, queue):
    filename = "head_"+node+"_"+str(k)+".lp"
    local_rules = run_subtask(filename, graph.node[node]["predicates"], defining_rules_of_predecessors)
    queue.put(local_rules)

def compute_component_rules(component, component_solutions_queue):
    if len(component) == 1:
        compute_rules(list(component)[0],'',0,component_solutions_queue)
    else:
        component_rules = set()
        subcomponent_processes = []
        subcomponent_solutions = []
        subcomponent_solutions_queue = Queue()

        subgraph = graph.subgraph(component)
        leaves = [x for x in subgraph.nodes_iter() if subgraph.out_degree(x) == 0]
        subgraph.remove_nodes_from(leaves)
        subcomponents = list(nx.connected_components(subgraph.to_undirected()))
        if len(subcomponents) == 1:
            compute_component_rules(subcomponents[0], subcomponent_solutions_queue)
            defining_rules = subcomponent_solutions_queue.get()
            if defining_rules == set(['no_solution']):
                component_solutions_queue.put(set(['no_solution']))
                return
        else:
            for subcomponent in subcomponents:
                p = Process(target = compute_component_rules, args = (subcomponent, subcomponent_solutions_queue))
                subcomponent_processes.append(p)
                p.start()
            subcomponent_solutions = [subcomponent_solutions_queue.get() for p in subcomponent_processes]
            for p in subcomponent_processes:
                p.join()

            for subsol in subcomponent_solutions:
                if subsol == set(['no_solution']):
                    component_solutions_queue.put(set(['no_solution']))
                    return

            defining_rules = itertools.product(*subcomponent_solutions)

        for k, defining_rules_group in enumerate(defining_rules):
            leave_rules = []
            leave_processes = []
            leave_queue = Queue()

            defining_rules_combinaton = ''
            for rule in defining_rules_group:
                defining_rules_combinaton += rule
            if len(leaves) == 1:
                compute_rules(leaves[0], defining_rules_combinaton, k, leave_queue)
                leave_rules = [leave_queue.get()]
            else:
                for leave in leaves:
                    p = Process(target = compute_rules, args = (leave, defining_rules_combinaton, k, leave_queue))
                    leave_processes.append(p)
                    p.start()
                leave_rules = [leave_queue.get() for p in leave_processes]
                for p in leave_processes:
                    p.join()

            for learul in leave_rules:
                if learul == set(['no_solution']):
                    component_solutions_queue.put(set(['no_solution']))
                    return

            leave_rules.append(set([defining_rules_combinaton]))
            for rule_group in itertools.product(*leave_rules):
                new_component_rule = ''
                for rule in rule_group:
                    new_component_rule += rule
                component_rules.add(new_component_rule)

        component_solutions_queue.put(component_rules)

def run_non_head_examples():
    if "non-head" in example_indizes:
        filename = "non_head.lp"
        fwrite = open(filename,"w")
        for i in example_indizes["non-head"]:
            fwrite.write(lines[i]+"\n")
        for i in line_indizes:
            fwrite.write(lines[i]+"\n")
        fwrite.close()
        component_solutions.append(get_rules(filename))
        # delete temporary file
        os.remove(filename)

# input: an atom
# output: a list with two elements - the first one contains the predicate symbol of the atom (NBF previously removed if present),
#         the second one is the list of all its arguments
def get_pred_args(atom):
    # handle tuple types
    atom = re.sub(r'\(\(','(',re.sub(r'\)\)',')',atom))
    if '(' in atom:
        declaration = atom.split('(')
        predicate = declaration[0]
        arguments = declaration[1].split(')')[0].split(',')
    else:
        predicate = atom
        arguments = []
    # handles NBF
    if predicate.startswith("not "):
        predicate = predicate[4:]
    return [predicate, arguments]

# input: a list of input or output type constants
# output: a list of two lists - the first one contains all the input predicates, the second one - all the output predicates
def process_arguments(args):
    in_arg = set()
    out_arg = set()
    for arg in args:
        if arg[0] == '+':
            in_arg.add(arg[1:])
        elif arg[0] == '-':
            out_arg.add(arg[1:])
    return [in_arg, out_arg]

# input: graph, a node to be removed, list of its immediate predecessors, list of its immediate successors
# side effects: all the outgoing edges of the node are recreated from all of its immediate predecessors,
#               all the incoming edges of the node bypass it to all of its immediate successors,
#               the node is removed
def bypass_and_remove_node(graph, node, predecessors, successors):
    for source_node, destination_node in graph.edges():
        if source_node == node:
            for p in predecessors:
                graph.add_edge(p,destination_node)
        elif destination_node == node:
            for s in successors:
                graph.add_edge(source_node,s)
    graph.remove_node(node)

# input: graph, non-empty list of nodes to be merged,
#        node n to be merged into (a string, which serves as its name, currently non-existing in the graph)
#        list of head predicates predicates_of_node of the node that is to be created
# side effects: after execution, graph does not contain any of the nodes to be merged
#        n is created, adjacent to all the edges of the nodes to be merged and with a predicates attribute equal to predicates_of_node
def merge_nodes(graph, nodes, n, predicates_of_node):
    graph.add_node(n, predicates = predicates_of_node)

    for source_node, destination_node in graph.edges():
        if source_node in nodes:
            graph.add_edge(n,destination_node)
        elif destination_node in nodes:
            graph.add_edge(source_node,n)

    for node in nodes:
        graph.remove_node(node)

# the if statement is needed so that the functions from above can be imported on Windows without running the code below
if __name__ == "__main__":
    # handles unexpected calls
    if not 1 < len(sys.argv) < 4:
        print "Usage: python parallelizer.py (--optimal) <inputFileName>"

    # PART 2 parses the input file

    else:
        # the following three structures are used to keep account of different types of lines and are used to produce the ASPAL subprograms
        # dictionary of (predicate, index) pairs corresponding to head declaration lines
        head_indizes = {}
        # dictionary of (predicate, index) pairs corresponding to positive example lines
        example_indizes = {}
        # indizes of all other non-blank lines
        line_indizes = []
        # the following three dictionaries are used to produce edges in the dependency graph
        # dictionary of (head_predicate, [defining_predicates]) pairs
        heads = {}
        # dictionary of (body_predicate, [[defining_predicates],[defined_predicates]]) pairs
        bodies = {}
        # dictionary of (head_predicate, [defining_predicates]) pairs for rules with a non-empty body
        rules = {}

        # read program from input file
        if (len(sys.argv) == 2):
            f=open(sys.argv[1],"r")
        else:
            f=open(sys.argv[2],"r")
        program = f.read()
        f.close()
        # delete comments (everything between the characters '%' and ('\n' or $)),
        # then spaces except in between not and the predicate symbol in case of NBF,
        # subsequently add a newline character after each dot, if it is not enclosed in brackets - ()
        no_blanks_program = re.sub(r'\.(?![^\(]*\))','.\n',re.sub(r'(?<!not)\s','',re.sub(r'\%.*(?:$|\n)','', program)))
        # don't redefine the variable lines elsewhere! It's needed for the creation of ASPAL subprograms
        lines = no_blanks_program.splitlines()

        # create the lists of dependencies according to head declarations, body declarations and rules
        for i, parsed_l in enumerate(lines):
            # skip empty lines
            if parsed_l.strip():
                # assume unique head declaration predicates and no NBF in them
                if parsed_l.startswith("modeh("):
                    atom = parsed_l[6:-2]
                    atom_struct = get_pred_args(atom)
                    predicate = atom_struct[0]
                    arguments = atom_struct[1]
                    if predicate in heads:
                        heads[predicate].append(process_arguments(arguments)[0])
                        head_indizes[predicate].append(i)
                    else:
                        heads[predicate] = [process_arguments(arguments)[0]]
                        head_indizes[predicate] = [i]

                elif parsed_l.startswith("modeb("):
                    line_indizes.append(i)
                    atom = parsed_l[6:-2]
                    atom_struct = get_pred_args(atom)
                    predicate = atom_struct[0]
                    arguments = atom_struct[1]
                    processed_arguments = process_arguments(arguments)
                    #checks if key already present in bodies
                    if predicate in bodies:
                        bodies[predicate].append(processed_arguments)
                    else:
                        bodies[predicate] = [processed_arguments]

                elif parsed_l.startswith("example("):
                    last_comma_index = parsed_l.rfind(',')
                    atom = parsed_l[8:last_comma_index]
                    predicate = get_pred_args(atom)[0]
                    if predicate in example_indizes:
                        example_indizes[predicate].append(i)
                    else:
                        example_indizes[predicate] = [i]

                else:
                    line_indizes.append(i)
                    # consider only rules with non-empty heads and bodies for the dependency graph, assume no NBF in the head
                    rule = parsed_l.split(':-')
                    if len(rule) > 1 and rule[0]:
                        head_atoms = rule[0]
                        # handles choice rules
                        if '{' in head_atoms:
                            head_atoms = head_atoms[head_atoms.index('{')+1:head_atoms.index('}')]
                        for head_atom in head_atoms.split(','):
                            head_predicate = get_pred_args(head_atom)[0]
                            body_atoms = rule[1][:-1]
                            body_predicates = set()
                            # obtain the predicates of the body atoms between ':-' and '.'
                            separators = []
                            open_bracket = False
                            for i, char in enumerate(body_atoms):
                                if char == '(':
                                    open_bracket = True
                                elif char == ')':
                                    open_bracket = False
                                elif char == ',' and not open_bracket:
                                    separators.append(i+1)
                            # additional separators at the beginning and the end of the list
                            separators.insert(0,0)
                            separators.append(len(body_atoms)+1)
                            for i in xrange(len(separators)-1):
                                current_position = separators[i]
                                next_position = separators[i+1]-1
                                body_predicates.add(get_pred_args(body_atoms[current_position:next_position])[0])
                            #checks if key already present in rules
                            if head_predicate in rules:
                                rules[head_predicate].update(body_predicates)
                            else:
                                rules[head_predicate] = body_predicates

        #print heads
        #print bodies
        #print rules

        # PART 3 creates a dependency graph with edges of (defining predicate, dependant predicate) pairs,
        # redistributes positive examples of non-head predicates among the responsible head predicates
        # in order to enable non-observational predicate learning

        graph = nx.DiGraph()

        for h in heads:
            graph.add_node(h,predicates=[h])

        for h, deps in heads.iteritems():
            remaining_bodies = dict(bodies)
            for di in deps:
                for d in di:
                    if d in heads:
                        graph.add_edge(d,h)
                
                added_predicates = True
                predicate_types = di

                while added_predicates:
                    added_predicates = False
                    for b, bdeps in remaining_bodies.iteritems():
                        for depi in bdeps:
                            if depi[0].issubset(predicate_types):                                
                                predicate_types.update(depi[1])
                                added_predicates = True
                                graph.add_edge(b,h)
                                break
                        if added_predicates == True:
                            break
                    if added_predicates == True:
                        remaining_bodies.pop(b)

        for r, deps in rules.iteritems():
            for d in deps:
                graph.add_edge(d,r)
        
        non_observational_predicates = set(example_indizes.keys()).difference(set(heads.keys()))
        for predicate in non_observational_predicates:
            if predicate not in rules:
                print "No solutions."
                sys.exit()
            responsible_predicates = rules[predicate]
            responsible_head_predicates = list(responsible_predicates.intersection(set(heads.keys())))
            if responsible_head_predicates:
                merge_nodes(graph, responsible_predicates, predicate, responsible_head_predicates)
                heads[predicate] = []
                first = responsible_head_predicates[0]
                if first in example_indizes:
                    example_indizes[first].extend(example_indizes[predicate])
                else:
                    example_indizes[first] = example_indizes[predicate]
            else:
                if "non-head" in example_indizes:
                    example_indizes["non-head"].extend(example_indizes[predicate])
                else:
                    example_indizes["non-head"] = example_indizes[predicate]
            example_indizes.pop(predicate)


        # remove all non-head nodes of the graph (bypass them and create new edges to keep the graph structure)
        for node in graph.nodes():
            if not node in heads:
                bypass_and_remove_node(graph, node, graph.predecessors(node), graph.successors(node))

        # remove all self-loops (if present)
        for node in graph.nodes():
            try:
                graph.remove_edge(node,node)
            except:
                pass

        # merge nodes belonging to a cycle into a single node if at least one head predicate is involved
        cycle_detected = True
        k = 0
        while cycle_detected:
            cycle_detected = False
            cycles = list(nx.simple_cycles(graph))
            for cycle in cycles:
                if cycle:
                    cycle_detected = True
                    predicates_of_node = []
                    for node in cycle:
                        predicates_of_node.extend(graph.node[node]["predicates"])
                    merge_nodes(graph, cycle, "cycle_"+str(k), predicates_of_node)
                    break
            k += 1

        '''
        # at this point, each node in the graph corresponds to a head declaration or a cycle containing at least one head declaration
        print graph.nodes()

        # output dependancies
        print "Sets of dependancies:"
        transposed_graph = nx.reverse(graph)
        for n in graph.nodes():
            print n, ":", nx.descendants(transposed_graph,n)
        '''

        # PART 4 launches a subprocess for each connected component in the dependency graph

        # a list of processes for each connected component of the dependency graph
        component_processes = []
        # a list of rules for each connected component of the dependency graph
        component_solutions = []
        # a queue for the parallel processes (one for each component) to store their output
        component_solutions_queue = Queue()

        for component in nx.connected_components(graph.to_undirected()):
            p = Process(target = compute_component_rules, args = (component,component_solutions_queue))
            component_processes.append(p)
            p.start()

        # don't join before getting the solutions from the queue - if it gets overfull, the program deadlocks!
        component_solutions = [component_solutions_queue.get() for p in component_processes]
        for p in component_processes:
            p.join()

        # handles the case in which there are some examples to be covered by the background knowledge alone
        run_non_head_examples()

        # PART 5 postprocesses the solutions of the subprocesses launched in the previous part and prints out the solutions of the original task
        solutions_present = True
        for comsol in component_solutions:
            if comsol == set(['no_solution']):
                solutions_present = False
                break

        if solutions_present:
            solutions = itertools.product(*component_solutions)
            #print solutions
            print "\n\n\n####################################\nFinal output\n####################################\n\n"
            for i, s in enumerate(solutions):
                print '\n----Solution {0}----\n'.format(str(i+1))
                new_solution = ''
                for r in s:
                    new_solution += r
                print new_solution