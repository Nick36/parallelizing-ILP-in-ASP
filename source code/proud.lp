modeh(proud(+parent)). 
modeh(scientist(+child)). 
modeh(explorer(+child)). 
modeh(lonely(+childless)).

modeb(scientist(+child)). 
modeb(explorer(+child)). 
modeb(adventurous(+child)).
modeb(curious(+child)).
modeb(offspring(+parent,-child)).

humanist(X) :- scientist(X). 
child(annika). 
child(tommy).
child(jack).
parent(john).
parent(clara).
childless(persephone). 
offspring(clara,annika).
offspring(john,jack). 
adventurous(tommy).
curious(annika).

example(humanist(tommy),-1).
example(humanist(annika),1).
example(explorer(tommy),1).
example(explorer(annika),-1).
example(proud(clara),1).
example(proud(john),-1).
example(lonely(persephone),1).
