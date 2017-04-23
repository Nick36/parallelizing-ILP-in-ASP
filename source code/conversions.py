#!/usr/bin/env python

import getopt, sys
import re



def fix_lists(line):
    pass

def carcino_atoms(file):
    atoms = set()
    f = open(file, 'r')
    for line in f:
        a = re.split('\(|,|\)',line)
        for word in a:
            if word.startswith('d'):
                atoms.add(word)
    for x in atoms:
        print "atom({0}).".format(x)


def carcino_ashby_alert(file, n = 2):
    f = open(file, 'r')
    for line in f:
        a = re.split(',|\]',line)
        if len(a) > 1:
            acc = ''
            
            for w in range(0,n):

                acc += a[w]+ ','
            for w in range(1, len(a)):
                #print "Current " + a[w]
                q = a[w].replace('[', '').replace('\)', '').replace('\n', '')
                if not ')' in q:
                    print "has_"+acc + q + ').'


def real_to_int(file):
    f = open(file, 'r')
    charge = set()
    integer = set()
    for line in f:
        sea =re.search('0\.[0-9]+', line)
        if not sea:
            sea =re.search('[0-9]\.[0-9]+', line)
        if sea:
            seax = line[sea.start():sea.end()]
            num = int(float(seax) * 1000)
            charge.add(str(num))
            e = line.replace(seax, str(num))
            print e,
        else:
            print line,
        sea =re.search(',[0-9]+', line)
        if sea:
            seax = line[sea.start()+1:sea.end()]
            integer.add(seax)
    for i in charge:
        print 'charge({0}).'.format(i)
    for i in integer:
        print 'integer({0}).'.format(i)




def main():

    #Checking the inputs
    try:
        opts, args = getopt.getopt(sys.argv[1:], "h", ["help", "all", "carcinoatoms=", "carcinoashby=", "rti=", "newg="])
    except getopt.GetoptError, err:
        # print help information and exit:
        print str(err)
        # will print something like "option -a not recognized"
        sys.exit(2)
    #Default options
    for o, a in opts:

        if o in ("-h", "--help"):
            sys.exit()
        elif o in ("--carcinoatoms"):
            carcino_atoms(a)
        elif o in ("--carcinoashby"):
            carcino_ashby_alert(a)
        elif o in ("--rti"):
            real_to_int(a)
        elif o in ("--newg"):
            carcino_ashby_alert(a,1)
        else:
            assert False, "unhandled option"


if __name__ == "__main__":
    main()