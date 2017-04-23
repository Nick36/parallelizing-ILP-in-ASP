from UserList import UserList
import string

class CList(UserList):
    emptyword=''

    def __init__(self, list, emptyword=''):
        UserList.__init__(self,list)
        self.emptyword = emptyword
        

    def __str__(self):
        return self.cstmString(self.emptyword)

    def addSuffixToAllElements(self, suffix):
        out = []
        for e in self:
            q=str(e) + suffix
            out.append(q)
        return out


    def addPrefixToAllElements(self, prefix):
        out = []
        for e in self:
            q=prefix+str(e)
            out.append(q)
        return out


    def toTypedList(self, type):
        out = []
        for inp in range(len(self)):
            out.append(type+'('+str(self[inp])+')')
        return out

    def toTypedString(self, type):
        if self == []:
            return type
        else:
            return type+'('+str(self)+ ')'

    def cstmString(self, emptyword):
        if self == []:
            return emptyword
        return string.replace(UserList.__str__(self)[1:-1], '\'', '')