__author__ = 'dc'

import time


def extract_stat_from_line(line, separator = ':', ingnoreseparator = "("):
    nss = line.replace('\n', '')
    ns = nss.replace(' ', '')

    r = ns.split(separator, 1)
    if len(r) < 2:
        return None, None
    key = r[0].replace('.', '')
    value = r[1].split(ingnoreseparator)
    return key.lower(), value[0]
    

class Stats():
    """
    There's a set of interesting keywords that can be taken
    from strings. When we find it we update the current value.
    """

    def __init__(self):
        self.start_time = time.time()
        self.allstats = dict()

        
        self.allstats['max_conditions'] =  0
        self.allstats['max_rules'] =  0
        self.allstats['max_consumers'] =  0
        self.allstats['max_producers'] =  0
        self.allstats['optimal'] =  None
        self.allstats['all'] =  None


        self.allstats['total_skeleton_rules'] =  0




        self.allstats['total_time'] =  0

        self.allstats['iterations'] =  0


        self.allstats['models'] =  0
        self.allstats['time'] =  0
        self.allstats['prepare'] =  0
        self.allstats['prepro'] =  0
        self.allstats['choices'] =  0
        self.allstats['conflicts'] =  0
        self.allstats['restarts'] =  0

        self.allstats['atoms'] =  0
        self.allstats['rules'] =  0
        self.allstats['bodies'] =  0
        self.allstats['equivalences'] =  0

        self.allstats['variables'] =  0
        self.allstats['constraints'] =  0
        self.allstats['lemmas'] =  0
        self.allstats['conflicts'] =  0
        self.allstats['loops'] =  0
        self.allstats['deleted'] =  0

        self.allstats['solutions'] =  0

        self.allstats['tight'] =  'Unknown'

    def startTime(self):
        self.start_time = time.time()

    def stopTime(self):
        self.allstats['total_time'] = time.time() - self.start_time

    #Tries to parse some interesting stat
    def checkStatUpdate(self, line, set = False):
        key,value = extract_stat_from_line(line)
        if key == 'tight':
            self.allstats['tight'] = value
        elif key == 'models':
            self.allstats['models'] = value
        elif not key == None and self.allstats.has_key(key):
            if not set:
                self.allstats[key] =  self.allstats[key] + float(value)
            else:
                self.allstats[key] =  value
        else:
            return False
        return True

    def printall(self):
        for k,v in self.allstats.iteritems():
            print str(k)+': '+ str(v)



