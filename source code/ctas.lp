

modeh(proscribed(#event,+timepoint,+scenario)).
modeh(required(#event,+timepoint,+scenario)).

modeh(uTS_prechart(#event,+timepoint,+scenario,#learning_uni_trigger)).

modeh(eTS_prechart(#event,+timepoint,+scenario,#learning_exist_trigger)).
modeh(hyp_happens(#event,+timepoint,+timepoint,+scenario)).

modeb(holds_at(#fluent,+timepoint,+scenario)).
modeb(holds_at_before(#fluent,+timepoint,+scenario)).
modeb(holds_at_before_before(#fluent,+timepoint,+scenario)).

modeb(not_holds_at(#fluent,+timepoint,+scenario)).

modeb(happens(#event,+timepoint,+scenario)).
modeb(next(+timepoint,+timepoint)).

modeb(hyp_holds_at(#fluent,+timepoint,+timepoint,+scenario)).
modeb(hyp_not_holds_at(#fluent,+timepoint,+timepoint,+scenario)).


%
%uTS_prechart(set_preupd,X1,X2,uni1) :- 
%	hyp_not_holds_at(preUpdating,X1,X1,X2),
%	timepoint(X1),scenario(X2).
% 
% --*** DOMAIN INDEPENDENT AXIOMS ***---

% (EC1)
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

% (EC2)
declipped(T1,F,T2,S) :- timepoint(T),
                      timepoint(T1),
                      timepoint(T2),
                      fluent(F),
                      event(E),
		      scenario(S),
                      happens(E,T,S),
                      T1<=T,
                      T<T2,
                      initiates(E,F,T).

% (EC3)
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

% (EC4)
started_in(T1,F,T2,S) :- timepoint(T),
                       timepoint(T1),
                       timepoint(T2),
                       fluent(F),
                       event(E),
			scenario(S),
                       happens(E,T,S),
                       T1<T,
                       T<T2,
                       initiates(E,F,T).



% (EC5)
holds_at_before(F,T2,S) :- 	timepoint(T1), timepoint(T2),
				next(T2,T1),fluent(F),
				scenario(S),
				holds_at(F,T1,S).

holds_at_before_before(F,T2,S) :- 	timepoint(T1), timepoint(T2),
				next(T,T1), timepoint(T), next(T2,T), fluent(F),
				scenario(S),
				holds_at(F,T1,S).

                     
% (EC5)
holds_at(F,T2,S) :- 	timepoint(T1),
                      	timepoint(T2),
                      	fluent(F),
                      	event(E),
			scenario(S),
                      	happens(E,T1,S),
                      	initiates(E,F,T1),
                      	T1<T2,             
                      	not stopped_in(T1,F,T2,S).


% (EC6)
not_holds_at(F,T2,S) :- 
			timepoint(T1),
                      	timepoint(T2),
                      	fluent(F),
                      	event(E),scenario(S),
                      	happens(E,T1,S),
                      	terminates(E,F,T1),
                      	T1<T2,
                      	not started_in(T1,F,T2,S).
	
% (EC7)
holds_at(F,T2,S) :- 	timepoint(T1),
                  	timepoint(T2),
                  	fluent(F), scenario(S),
                  	holds_at(F,T1,S),
                  	T1<T2,
                  	not clipped(T1,F,T2,S).

% (EC8)
not_holds_at(F,T2,S) :- timepoint(T1),
                   	timepoint(T2),
                   	fluent(F),scenario(S),
                   	not_holds_at(F,T1,S),
                   	T1<T2,
                   	not declipped(T1,F,T2,S).


not_initially(F,S):- fluent(F), scenario(S), not initially(F,S).

not_holds_at(F,0,S):- fluent(F), scenario(S), not_initially(F,S).

holds_at(F,0,S):- fluent(F), scenario(S), initially(F,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Event Occurrences 

% a required transition has happened after being executed
req_happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),				
		executed(A,P,S), required(A,P,S).

% a maybe transition has happened after being executed
may_happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),				
		 executed(A,P,S),maybe(A,P,S).

happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),
		may_happens(A,P,S).
happens(A,P,S):-  
		event(A),scenario(S), timepoint(P),
		req_happens(A,P,S).


% a transition that is not required or proscribed
%is a maybe transition 

maybe(A,T,S):-  
			event(A),scenario(S), timepoint(T),				
			not required(A,T,S),
			not proscribed(A,T,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


 % --*** CONSTRAINTS  ***--- 

:- timepoint(T),            
	event(A),scenario(S),
	required(A,T,S), 
	proscribed(A,T,S).


:- fluent(F),scenario(S),
	initially(F,S),
	not_initially(F,S).

:- timepoint(T),            
	event(A1),event(A2), 
	A1 != A2, scenario(S), 
	executed(A1,T,S),
	executed(A2,T,S).


:- timepoint(T),            
	fluent(F),
	scenario(S),
	holds_at(F,T,S), 
	not_holds_at(F,T,S).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% --*** TYPES  ***--- 
%%%%%%%%%%%%%%%%%%%%%%%%%%

client_Actions(yes_1;no_1).
cm_Actions(set_preupd;set_preupd_1;set_upd;set_upd_1;get_new_wthr_1;set_postupd; set_postupd_1).
cm_Actions(set_prerevert; set_prerevert_1).

event(E):- client_Actions(E).
event(E):- cm_Actions(E).

timepoint(0..6).

fluent(preUpdating;f_set_preupd;f_set_preupd_1;f_set_upd;f_set_upd_1).

scenario(s1).

in_scope(E,S):-event(E),scenario(S),happens(E,_,S).
in_scope(set_preupd,uni1).
in_scope(set_upd,uni1).
in_scope(set_upd_1,uni1).

in_scope(set_preupd,exist1).
in_scope(set_upd,exist1).
in_scope(set_upd_1,exist1).


learning_uni_trigger(uni1).
learning_exist_trigger(exist1).

trigger(TS):- learning_uni_trigger(TS).
trigger(TS):- learning_exist_trigger(TS).
trigger(TS):- bk_trigger(TS).


next(1,0).next(2,1).next(3,2).
next(4,3).next(5,4).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domain dependent axioms
%%%%%%%%%%%%%%%%%%%%%%%%%

% --FROM FLUENT DEFINITIONS ---

initiates(set_preupd,preUpdating ,T):- timepoint(T).
terminates(set_preupd_done ,preUpdating ,T):- timepoint(T).


initiates(set_preupd,f_set_preupd,T):- timepoint(T).
terminates(E, f_set_preupd,T):- event(E), E != set_preupd, timepoint(T).

initiates(set_preupd_1,f_set_preupd_1,T):- timepoint(T).
terminates(E, f_set_preupd_1,T):- event(E), E != set_preupd_1, timepoint(T).


initiates(set_upd,f_set_upd,T):- timepoint(T).
terminates(E, f_set_upd,T):- event(E), E != set_upd, timepoint(T).

initiates(set_upd_1,f_set_upd_1,T):- timepoint(T).
terminates(E, f_set_upd_1,T):- event(E), E != set_upd_1, timepoint(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% A required transition must be either 
% required existentially or universally
% at some time in the past.

:-
	timepoint(T), scenario(S),
	event(E),
	required(E,T,S),
	not uTS_prechart_satisfied_previously(E,T,S),
	not eTS_prechart_satisfied_previously(E,T,S).
%
%-----------------------------------------------
% (AUX1)
% The event  E has happened between time point T1 and T2 
% in scenario S
happens_in_between(E,T1,T2,S):- 
			timepoint(T1), timepoint(T2),
			event(E),scenario(S),
			timepoint(T), 
			T1<=T, T<T2, 
			happens(E,T,S).

req_happens_in_between(E,T1,T2,S):- 
			timepoint(T1), timepoint(T2),
			event(E),scenario(S),
			timepoint(T), 
			T1<=T, T<T2, 
			req_happens(E,T,S).

% an event in the scope of the triggered scenario
% has happend 

happens_event_in_scope(T1,T2,S,TS):- 
		timepoint(T1),timepoint(T2),
		T1<T2, scenario(S), 
		trigger(TS),
		event(E2), 
		in_scope(E2,S), 
		happens_in_between(E2,T1,T2,S).


%--------------------------------------------------------------------

% A required transition occurs sometime after T in scenario S
req_happens_eventually(E,T,S):-
	timepoint(T), scenario(S),
	event(E), timepoint(T2), 
	T<=T2,
	req_happens(E,T2,S).


% E occurs at time point T2 after T
next_req_happens(E,T,T2,S):-
	timepoint(T), scenario(S),
	event(E), timepoint(T2), 
	T<=T2,
	req_happens(E,T2,S).

%  the first E occurrence from T is at T2 
first_next_req_happens(E,T,T2,S):-
	timepoint(T), scenario(S),
	event(E), timepoint(T2), 
	T<=T2,
	req_happens(E,T2,S),
	not happens_in_between(E,T,T2,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Universal Scenarios
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The prechart of a universal scenario has been satisfied
% somepoint in the past

uTS_prechart_satisfied_previously(E,T,S):- 
	timepoint(T), scenario(S),
	event(E),
	timepoint(T0),T0<=T,
	trigger(Trig),
	uTS_prechart(E,T0,S,Trig). 

% It cannot be the case that a universal triggered scenario
% prechart has been satisfied in the pastand its main chart 
% is not satisfied with respect to the scope of the scenario

:-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	uTS_prechart(E,T,S,Trig),
	not req_happens_eventually(E,T,S).

:- 
	timepoint(T1), scenario(S),
	event(E), trigger(Trig),
	uTS_prechart(E,T1,S,Trig),
	req_happens_eventually(E,T1,S),
	timepoint(T2), T1<=T2,
	first_next_req_happens(E,T1,T2,S),
	event(E2), E != E2,
	in_scope(E2,Trig), 
	happens_in_between(E2,T1,T2,S).


proscribed(E2,T,S):- 
	event(E2),  scenario(S),
	trigger(Trig),
	in_scope(E2,Trig), 
	timepoint(T),timepoint(T1), 
	T1<=T,
	event(E), E != E2,
	uTS_prechart(E,T1,S,Trig),
	req_happens_eventually(E,T1,S),
	timepoint(T2), T1<=T2,T<=T2,
	first_next_req_happens(E,T1,T2,S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Existential Scenarios
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eTS_prechart_satisfied_previously(E,T,S):- 
	timepoint(T), scenario(S),
	event(E),
	timepoint(T0),T0<=T,
	trigger(Trig),
	not happens_event_in_scope(T0,T,S,Trig),
	eTS_prechart(E,T0,S,Trig).

:-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	eTS_prechart(E,T,S,Trig),
	not happens_eventually_in_scope(E,T,S,Trig),
	not reachable(E,T,S,Trig).

% E happens sometime after T and no events in the scope
% happen until then.
happens_eventually_in_scope(E,T1,S,Trig):-
	timepoint(T1), scenario(S),
	event(E), timepoint(T2), 
	trigger(Trig), in_scope(E,Trig),
	T1<=T2, happens(E,T2,S),
	not happens_event_in_scope(T1,T2,S,Trig).

happens_event_in_scope(T1,T2,S,Trig):-
	timepoint(T1), timepoint(T2), T1<T2,
	event(E2), scenario(S),trigger(Trig),event(E),
	in_scope(E,Trig), 
	happens_in_between(E,T1,T2,S).



% The below is to reason about other branches
% that can emerge from any time point in the given scenario

hyp_holds_at(F,T,T,S):-
	fluent(F),
	timepoint(T), 0<=T, scenario(S),
	holds_at(F,T,S).

hyp_not_holds_at(F,T,T,S):-
	fluent(F),
	timepoint(T), 0<=T, scenario(S),
	not_holds_at(F,T,S).


hyp_proscribed(E,T0,T0,S):-
	timepoint(T0),
	scenario(S),
	event(E),
	proscribed(E,T0,S).

:-
	 timepoint(T0),
	scenario(S),
	event(E),
	proscribed(E,T0,S),
	hyp_happens(E,T0,T0,S).

:- 
	timepoint(T), scenario(S),
	event(E), timepoint(T0),
	T0<=T,
	hyp_happens(E,T,T0,S),
	hyp_proscribed(E,T,T0,S).


:- 
	timepoint(T), scenario(S),
	event(E), timepoint(T0),
	event(E2), E != E2,
	T0<=T,
	hyp_happens(E,T,T0,S),
	hyp_happens(E2,T,T0,S).
:- 
	timepoint(T2),  scenario(S),
	timepoint(T0), timepoint(T1), T0<=T1,
	T0<=T2, 
	T1<T2, event(E), event(E2),
	hyp_happens(E,T2,T0,S),
	not hyp_happens(E2,T1,T0,S).
 
hyp_reachable(E,T,S,Trig):-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	required(E,T,S).

hyp_reachable(E,T,S,Trig):-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	not required(E,T,S),
	event(E2), E != E2,
	not in_scope(E2,Trig),
	happens(E2,T,S),
	hyp_reachable(E,T+1,S,Trig).

reachable(E,T,S,Trig):-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	timepoint(T2), T<=T2,
	hyp_reachable(E,T,S,Trig).

reachable(E,T,S,Trig):-
	timepoint(T), scenario(S),
	event(E), trigger(Trig),
	timepoint(T2), T<=T2,
	hyp_reachable_from(E,T2,T,S,Trig).
	
hyp_reachable_from(E,T2,T0,S,Trig):-
	timepoint(T0), scenario(S),
	event(E), trigger(Trig),
	timepoint(T2), T0<=T2,
	not hyp_proscribed(E,T2,T0,S),
	hyp_happens(E,T2,T0,S).

hyp_reachable_from(E,T2,T0,S,Trig):-
	timepoint(T0), scenario(S),
	event(E), timepoint(T2),
	 T0<=T2,
	event(E2), E != E2,
	trigger(Trig),
	not in_scope(E2,Trig),
	not hyp_proscribed(E2,T2,T0,S),
	hyp_happens(E2,T2,T0,S),
	hyp_reachable_from(E,T2+1,T0,S,Trig).


%-----------------
	
% (Hyp EC1)
hyp_clipped(T1,F,T2,T0,S) :- timepoint(T),
                    timepoint(T1),timepoint(T0),
		T0<=T1,
                    timepoint(T2),	
                    fluent(F),
                    event(E), 
		    scenario(S),
                    hyp_happens(E,T,T0,S),
                    T1<=T,
                    T<T2,
                    terminates(E,F,T).

% (Hyp EC2)
hyp_declipped(T1,F,T2,T0,S) :- timepoint(T),
                      timepoint(T1),timepoint(T0),
			T0<=T1,
                      timepoint(T2),
                      fluent(F),
                      event(E),
		      scenario(S),
                      hyp_happens(E,T,T0,S),
                      T1<=T,
                      T<T2,
                      initiates(E,F,T).

% (Hyp EC3)
hyp_stopped_in(T1,F,T2,T0,S) :- timepoint(T),
                       timepoint(T1),
                       timepoint(T2),timepoint(T0),
			T0<=T1,
                       fluent(F),
                       event(E),
			scenario(S),
                       hyp_happens(E,T,T0,S),
                       T1<T,
                       T<T2,
                       terminates(E,F,T).

% (Hyp EC4)
hyp_started_in(T1,F,T2,T0,S) :- timepoint(T),
                       timepoint(T1),
                       timepoint(T2),timepoint(T0),
			T0<=T1,
                       fluent(F),
                       event(E),
			scenario(S),
                       hyp_happens(E,T,T0,S),
                       T1<T,
                       T<T2,
                       initiates(E,F,T).



% (Hyp EC5)
hyp_holds_at(F,T2,T0,S) :- 
			timepoint(T1),
                      	timepoint(T2),
                      	fluent(F),timepoint(T0),
			T0<T2, T0<=T1,T1<T2,
                      	event(E),
			scenario(S),
                      	hyp_happens(E,T1,T0,S),
                      	initiates(E,F,T1),
                      	not hyp_stopped_in(T1,F,T2,T0,S).

% (Hyp EC6)
hyp_not_holds_at(F,T2,T0,S) :- 
			timepoint(T1),
                      	timepoint(T2),timepoint(T0),
                      	fluent(F),
			T0<T2, T0<=T1,T1<T2,
                      	event(E),scenario(S),
                      	hyp_happens(E,T1,T0,S),
                      	terminates(E,F,T1),
                      	not hyp_started_in(T1,F,T2,T0,S).
	
% (Hyp EC7)
hyp_holds_at(F,T2,T0,S) :- 	
			timepoint(T1),
                  	timepoint(T2),timepoint(T0),
			T0<T2, T0<=T1,
                  	fluent(F), scenario(S),
                  	hyp_holds_at(F,T1,T0,S),
                  	T1<T2,
                  	not hyp_clipped(T1,F,T2,T0,S).

% (Hyp EC8)
hyp_not_holds_at(F,T2,T0,S) :- timepoint(T1),
                   	timepoint(T2),timepoint(T0),
                   	fluent(F),scenario(S),
			T0<T2, T0<=T1,
                   	hyp_not_holds_at(F,T1,T0,S),
                   	T1<T2,
                   	not hyp_declipped(T1,F,T2,T0,S).	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


uTS_prechart(set_postupd_1,T3,S,successful_update):- 
		scenario(S), 
		timepoint(T0), timepoint(T3),T0<T3,
		happens(set_upd,T0,S),timepoint(T1),T0<T1,
		first_next_req_happens(get_new_wthr_1,T0,T1,S),
		not happens_in_the_scope(T0,T1,S,successful_update), 
		timepoint(T2),T1<T2,
		first_next_req_happens(yes_1,T1,T2,S),
		not happens_in_the_scope(T1,T2,S,successful_update),
		next(T3,T2). 


uTS_prechart(set_postupd,T4,S,successful_update):- 
		scenario(S), 
		timepoint(T0), timepoint(T3),T0<T4,
		happens(set_upd,T0,S),timepoint(T1),T0<T1,
		first_next_req_happens(get_new_wthr_1,T0,T1,S),
		not happens_event_in_scope(T0,T1,S,successful_update), 
		timepoint(T2),T1<T2,
		first_next_req_happens(yes_1,T1,T2,S),
		not happens_event_in_scope(T1,T2,S,successful_update),
		timepoint(T3),T2<T3,
		first_next_req_happens(set_postupd_1,T2,T3,S),
		not happens_event_in_scope(T2,T3,S,successful_update),
		next(T4,T3).

in_scope(successful_update, set_upd).
in_scope(successful_update, get_new_wthr_1).
in_scope(successful_update, yes_1).
in_scope(successful_update, set_postupd_1).
in_scope(successful_update, set_postupd).

bk_trigger(successful_update).

uTS_prechart(set_prerevert_1,T3,S,failed_update):- 
		scenario(S), 
		timepoint(T0), timepoint(T3),T0<T3,
		happens(set_upd,T0,S),timepoint(T1),T0<T1,
		first_next_req_happens(get_new_wthr_1,T0,T1,S),
		not happens_event_in_scope(T0,T1,S,failed_update), 
		timepoint(T2),T1<T2,
		first_next_req_happens(no_1,T1,T2,S),
		not happens_event_in_scope(T1,T2,S,failed_update),
		next(T3,T2). 


uTS_prechart(set_prerevert,T4,S,failed_update):- 
		scenario(S), 
		timepoint(T0), timepoint(T3),T0<T4,
		happens(set_upd,T0,S),timepoint(T1),T0<T1,
		first_next_req_happens(get_new_wthr_1,T0,T1,S),
		not happens_event_in_scope(T0,T1,S,failed_update), 
		timepoint(T2),T1<T2,
		first_next_req_happens(no_1,T1,T2,S),
		not happens_event_in_scope(T1,T2,S,failed_update),
		timepoint(T3),T2<T3,
		first_next_req_happens(set_prerevert_1,T2,T3,S),
		not happens_event_in_scope(T2,T3,S,failed_update),
		next(T4,T3).

in_scope(failed_update, set_upd).
in_scope(failed_update, get_new_wthr_1).
in_scope(failed_update, no_1).
in_scope(failed_update, set_prerevert_1).
in_scope(failed_update, set_prerevert).

bk_trigger(failed_update).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% -- Narrative --


executed(set_preupd,0,s1). required(set_preupd,0,s1).	
executed(set_upd,1,s1).	 %required(set_upd,1,s1).			
executed(get_new_wthr_1,2,s1). %required(get_new_wthr_1,2,s1).		
executed(yes_1,3,s1).	%required(yes_1,3,s1).	
executed(set_postupd_1,4,s1).	required(set_postupd_1,4,s1).	
executed(set_postupd,5,s1).	required(set_postupd,5,s1).	



 % --*** EXAMPLES ***---


example(req_happens(set_preupd,0,s1), 1).

%:- not req_happens(set_preupd,0,s1).
%
%
%#hide.
%#show event(_).
