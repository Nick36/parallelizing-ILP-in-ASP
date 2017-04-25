

modeh(proscribed(#event,+timepoint,+scenario)).
%modeh(0,8,min,required("#event","+timepoint","+scenario")).
modeh(req_happens(#event,+timepoint,+scenario)).

modeb(holds_at(#fluent,+timepoint,+scenario) , opt(o(max,1))).
modeb(not holds_at(#fluent,+timepoint,+scenario), opt(o(max,1))).

%goal(examples).

%************************
% --*** BACKGROUND ***---
%************************
 
% %%%%%%%%%%%%%%%%%%%%%%%%
% DOMAIN INDEPENDENT AXIOMS 
%%%%%%%%%%%%%%%%%%%%%%%%%

clipped(T1,F,T2,S) :- timepoint(T),
                    timepoint(T1),
                    timepoint(T2),	
                    fluent(F),
                    event(E), 
		    	scenario(S),
                    happens(E,T,S),
                    T1<=T,
                    T<T2,
                    terminates(E,F,T).

stopped_in(T1,F,T2,S) :- timepoint(T),
                       timepoint(T1),
                       timepoint(T2),
                       fluent(F),
                       event(E),
				scenario(S),
                       happens(E,T,S),
                       T1<T,
                       T<T2,
                       terminates(E,F,T).

holds_at(F,T2,S) :- 	timepoint(T1),
                      	timepoint(T2),
                      	fluent(F),
                      	event(E),
				scenario(S),
                      	happens(E,T1,S),
                      	initiates(E,F,T1),
                      	T1<T2,             
                      	not stopped_in(T1,F,T2,S).

holds_at(F,T2,S) :- 	timepoint(T1),
                  	timepoint(T2),
                  	fluent(F), scenario(S),
                  	holds_at(F,T1,S),
                  	T1<T2,
                  	not clipped(T1,F,T2,S).

holds_at(F,0,S):- fluent(F), scenario(S), initially(F).


% Event Occurrences 
% -------------

req_happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),				
		executed(A,P,S), required(A,P,S).

may_happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),				
		 executed(A,P,S),maybe(A,P,S).

happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),
		may_happens(A,P,S).
happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),		
		req_happens(A,P,S).

maybe(A,T,S):-  
			event(A),scenario(S), timepoint(T),		
			not required(A,T,S),
			not proscribed(A,T,S).


% CONSTRAINTS   
% -------------

:- timepoint(T),            
	event(A),scenario(S), 
	required(A,T,S), 
	proscribed(A,T,S).

:- timepoint(T),            
	event(A),scenario(S), 
	req_happens(A,T,S), 
	proscribed(A,T,S).

:- fluent(F),scenario(S),
	timepoint(T),            
	req_happens(F,T,S),
	may_happens(F,T,S).


:- timepoint(T),            
	event(A1),event(A2), 
	A1 != A2, scenario(S), 
	executed(A1,T,S),
	executed(A2,T,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%
%  TYPES   
%%%%%%%%%%%%%%%%%%%%%%%%%%

event(start;logoutMsg;authenticate;sendMsg;logout;disable;enable).

timepoint(0..5).

fluent(loggedIn;registered).
fluent(flogoutMsg;fauthenticate;fsendMsg;flogout;fdisable;fenable).

scenario(s1;s2).

next(1,0).
next(2,1).
next(3,2).
next(4,3).
next(5,4).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domain dependent axioms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% --FROM FLUENT DEFINITIONS ---
 
% State fluents 
%--------------

initiates(enable,registered,T):- timepoint(T).
terminates(disable, registered,T):- timepoint(T).

initiates(authenticate, loggedIn,T):- timepoint(T).
terminates(logout, loggedIn,T):- timepoint(T).
terminates(disable, loggedIn,T):- timepoint(T).
 
% Event fluents 
%--------------

initiates(enable,fenable,T):- timepoint(T).
terminates(E, fenable,T):- event(E), E != enable, timepoint(T).

initiates(disable,fdisable,T):- timepoint(T).
terminates(E, fdisable,T):- event(E), E != disable, timepoint(T).

initiates(logout,flogout,T):- timepoint(T).
terminates(E, flogout,T):- event(E), E != logout, timepoint(T).

initiates(logoutMsg,flogoutMsg,T):- timepoint(T).
terminates(E, slogoutMsg,T):- event(E), E !=logoutMsg, timepoint(T).

initiates(sendMsg,fsendMsg,T):- timepoint(T).
terminates(E, fsendMsg,T):- event(E), E !=sendMsg, timepoint(T).

initiates(authenticate,fauthenticate,T):- timepoint(T).
terminates(E, fauthenticate,T):- event(E), E!=authenticate, timepoint(T).


% Deadlock free
%--------------

:- timepoint(T),            
	event(A1),scenario(S),
	not possible(T,S).

possible(T,S):-timepoint(T), scenario(S),
			event(E), not proscribed(E,T,S).


% Safety porperty
%--------------

 req_happens(logoutMsg,X1+1,X2):- 
		timepoint(X1),scenario(X2),
		happens(logout,X1,X2).



%  Narrative 
%--------------

initially(registered).

executed(enable,0,s1).	
executed(disable,1,s1).
executed(authenticate,2,s1).
		
executed(enable,0,s2).	
executed(authenticate,1,s2).	
executed(sendMsg,2,s2).	
executed(logout,3,s2).
executed(logoutMsg,4,s2).

%************************
% ---*** Examples ***----
%************************		


example(happens(enable,0,s1), 1).
example(happens(disable,1,s1),1).
example(happens(authenticate,2,s1), -1).
example(happens(enable,0,s2),1).
example(req_happens(authenticate,1,s2),1).
example(happens(sendMsg,2,s2),1).
example(happens(logout,3,s2), 1).
example(happens(logoutMsg,4,s2), 1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%




