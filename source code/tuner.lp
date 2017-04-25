

%Maximum number of body literals
option(max_body_literals, 2).

%Maximum number of rules
option(max_num_rules, 2).

option(max_output_list, 2).

modeh(proscribed(#event,+timepoint,+scenario)).
%modeh(0,8,min,required("#event","+timepoint","+scenario")).
modeh(req_happens(#event,+timepoint,+scenario)).

modeb(holds_at(#fluent,+timepoint,+scenario), [(max,1)]).
modeb(not holds_at(#fluent,+timepoint,+scenario), [(max,1)]).



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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% --*** TYPES  ***--- 
%%%%%%%%%%%%%%%%%%%%%%%%%%

tuner(t1_newValue;t1_dropReq;t1_restore).
switch(s_dropReq;s_dropReqAck_t1;s_restore).
user(t1_tune;start).
video_driver(blank;unblank;blank_Ack).
nonobservable(tau).

event(E):- tuner(E).
event(E):- switch(E).
event(E):- user(E).

timepoint(0..7).

fluent(waitingDropAck_t1;dropped_t1;tuning_t1;active_t1;blanked).
fluent(ft1_newValue;ft1_dropReq;ft1_restore;fs_dropReq;fs_dropReqAck_t1;fs_restore;ft1_tune).
scenario(s1;s2;s3;s4).

next(1,0).
next(2,1).
next(3,2).
next(4,3).
next(5,4).
next(6,5).
next(7,6).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domain dependent axioms
%%%%%%%%%%%%%%%%%%%%%%%%%

% --FROM FLUENT DEFINITIONS ---
 
initiates(set_Active_t1,active_t1,T):- timepoint(T).
terminates(set_Active_t2,active_t1,T):- timepoint(T).

initiates(t1_tune,tuning_t1,T):- timepoint(T).
terminates(s_restore,tuning_t1,T):- timepoint(T).
terminates(set_Active_t1,tuning_t1,T):- timepoint(T).
terminates(set_Active_t2,tuning_t1,T):- timepoint(T).

initiates(t1_dropReq,waitingDropAck_t1,T):- timepoint(T).
terminates(s_dropReqAck_t1,waitingDropAck_t1,T):- timepoint(T).

initiates(s_dropReqAck_t1,dropped_t1,T):- timepoint(T).
terminates(t1_restore,dropped_t1,T):- timepoint(T).

%initiates(blank, blanked,T):- timepoint(T).
%terminates(unblank, blanked,T):- timepoint(T).
 
% event fluents
initiates(s_dropReqAck_t1,fs_dropReqAck_t1,T):- timepoint(T).
terminates(E,fs_dropReqAck_t1,T):- timepoint(T), event(E), E != s_dropReqAck_t1.

initiates(t1_dropReq,ft1_dropReq,T):- timepoint(T).
terminates(E,ft1_dropReq,T):- timepoint(T), event(E), E != t1_dropReq.

initiates(t1_tune,ft1_tune,T):- timepoint(T).
terminates(E,ft1_tune,T):- timepoint(T), event(E), E != t1_tune.

initiates(t1_restore,ft1_restore,T):- timepoint(T).
terminates(E,ft1_restore,T):- timepoint(T), event(E), E != t1_restore.

initiates(s_restore,fs_restore,T):- timepoint(T).
terminates(E,fs_restore,T):- timepoint(T), event(E), E != s_restore.

initiates(set_Active_t1,fset_Active_t1,T):- timepoint(T).
terminates(E,fset_Active_t1,T):- timepoint(T), event(E), E !=set_Active_t1.

initiates(set_Active_t2,fset_Active_t2,T):- timepoint(T).
terminates(E,fset_Active_t2,T):- timepoint(T), event(E), E != set_Active_t2.

initiates(t1_newValue,ft1_newValue,T):- timepoint(T).
terminates(E,ft1_newValue,T):- timepoint(T), event(E), E != t1_newValue.

%--------------------------------------------------------------------

% Deadlock free
%--------------

:- timepoint(T),            
	event(A1),scenario(S),
	not possible(T,S).

possible(T,S):-timepoint(T), scenario(S),
			event(E), not proscribed(E,T,S).

%-----

%proscribed(t1_tune,T,S):-
%		timepoint(T), scenario(S),
%		holds_at(tuning_t1,T,S),
%		not_holds_at(waitingDropAck_t1,T,S),
%		not_holds_at(dropped_t1,T,S).

proscribed(t1_tune,T,S):-
		timepoint(T), scenario(S),
		not holds_at(active_t1,T,S).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% -- Narrative --

initially(active_t1).

happens(tau,0,s1).
executed(t1_tune,1,s1).


happens(tau,0,s2).
executed(t1_tune,1,s2).
executed(t1_newValue,2,s2). 
executed(t1_tune,3,s2).

%happens(tau,0,s3). 
%executed(t1_tune,1,s3). 
%executed(t1_newValue,2,s3). 
%executed(t1_dropReq,3,s3). 
%executed(t1_tune,4,s3). 
%executed(s_dropReqAck_t1,5,s3). 

%happens(tau,0,s4). 
%executed(t1_tune,1,s4). 
%executed(t1_newValue,2,s4). 
%executed(t1_dropReq,3,s4). 
%executed(s_dropReqAck_t1,4,s4). 
%executed(t1_restore,5,s4). 
%executed(t1_tune,6,s4). 

 % --*** EXAMPLES ***---


example(	req_happens(t1_tune,1,s1), 1).
example(	happens(t1_tune,1,s2), 1).
example(	happens(t1_newValue,2,s2), 1).
example(   	 happens(t1_tune,3,s2), -1).

	%happens(t1_dropReq,3,s3),
	%req_happens(t1_tune,4,s3),
	%happens(t1_dropReq,3,s4), 
	%happens(s_dropReqAck_t1,4,s4),
	%happens(t1_restore,5,s4),
	%not happens(t1_tune,6,s4). 



%%%%%%%%%%%%%%

