#!/usr/bin/env python

#from mpl_toolkits.mplot3d import axes3d
#import matplotlib.pyplot as plt
#import numpy as np

import getopt, sys


def processrange(ra):
        if ':' in ra:
            n1, n2 = ra.split(':')
            return range(int(n1),int(n2))
        else:
            a = ra.split(',')
            b = []
            for i in a:
                b.append(int(i))
            return b

def rearrangeAttributesFile(infilename, outfilename, selector, target, xatt):
    f=open(infilename, 'r')
    instring = f.read()
    f.close()
    outstring = rearrangeAttributes(instring, selector, target, xatt)
    f=open(outfilename, 'w')
    f.write(outstring)
    f.close()



def rearrangeAttributes(instring, selector, target, xatt):
    '''
    Consider the attributes
    conditions,rules,time,smthingelse
    0,1,12,i
    1,1,13,l
    0,2,4,ko
    1,2,44,k

    If selector = 'rules' and target = 'time' and xatt = 'conditions'
    then it produces
    conditions,1,2
    0,12,4
    1,13,44

    '''

    insplit = instring.split('\n')
    header = insplit[0]
    attributes = header.split(',')
    index_target = attributes.index(target)
    index_selector = attributes.index(selector)
    index_xatt = attributes.index(xatt)
    print "Indexes xatt:{0}, selector:{1}, target:{2}".format(str(index_xatt), str(index_selector), str(index_target))
    allines = insplit[1:]
    print "Converting"
    selectors = set()
    for l in allines:
        if len(l) > 1:
            sl = l.split(',')
            selectors.add(sl[index_selector])

    newlines = dict()

    for l in allines:
        if len(l) > 1:
            sl = l.split(',')
            
            if int(sl[index_xatt]) in newlines:
                    #Quick fix, actually this makes it work only for integers
                    newlines[int(sl[index_xatt])][int(sl[index_selector])] = sl[index_target]
            else:
                    newlines[int(sl[index_xatt])] = dict()
                    newlines[int(sl[index_xatt])][int(sl[index_selector])] = sl[index_target]
                
#           GOOD TO VISUALISE THE NESTED DICTIONARY
    print newlines
    


    #the assumption is that they all have the same keys
    #in other words there are no experiments with less rules
    outs = ''
    firstime = True
    for j in newlines.keys():
        if firstime:
            keys = newlines[j].keys()
            orderedkeys = sorted(keys)
            outs += xatt
            for ordk in orderedkeys:
                outs += ',' + str(ordk)
            firstime = False
            outs += '\n'
        outs += str(j)
        keys = newlines[j].keys()
        orderedkeys = sorted(keys)
        for ok in orderedkeys:
            outs += ','+ str(newlines[j][ok])
        outs += '\n'

    print outs
    return outs
    

class AspalGraph():



    def __init__(self, targets, i1, i1range = 1, i2=None, i2range = [1]):
        self.targets = targets
        self.i1 = i1
        self.i2 = i2
        if isinstance(i1range, str):
            i1range = processrange(i1range)
        if isinstance(i2range, str):
            i2range = processrange(i2range)

        self.i1range = i1range
        self.i2range = i2range
        self.points = []

    def __str__(self):
        s = ''
        for i in self.targets:
            s+=str(i)+','
        return "Targets: {0}".format(s[:-1]) + \
            "\nI1: {0}".format(self.i1)+\
            "\nI1Range: {0}".format(str(self.i1range))+\
            "\nI2: {0}".format(self.i2) + \
            "\nI2Range: {0}".format(str(self.i2range))

    def csvheader(self):
        s = str(self.i1)+','
        if self.i2:
            s+= str(self.i2)+','
        for i in self.targets:
            s+=str(i)+','
        return s[:-1]


    def makeGraph(self):
#        fig = plt.figure()
#        ax = fig.add_subplot(111, projection='3d')
#        X, Y, Z = axes3d.get_test_data(0.05)
#        ax.plot_wireframe(X, Y, Z, rstride=10, cstride=10)
#
#        plt.show()
        pass





def main():

    try:
        opts, args = getopt.getopt(sys.argv[1:], "p:", ["process="])
    except getopt.GetoptError, err:
        # print help information and exit:
        print str(err)
        # will print something like "option -a not recognized"
        sys.exit(2)
    #Default options
    filename = 'default'
    for o, a in opts:
        if o in ("-p", "--process"):
            filename = a
        else:
            assert False, "unhandled option"

    rearrangeAttributes(filename, filename+".new", 'max_rules', 'total_time', 'max_conditions' )


if __name__ == "__main__":
    main()