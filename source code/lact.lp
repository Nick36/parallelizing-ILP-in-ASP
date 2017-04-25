modeh(happens(use(#sugar),+timex), [name(hu)]).
modeb(holdsAt(#fluent,+timex), [(max, 2)]).
modeb(not holdsAt(#fluent,+timex), [(max, 2)]).



holdsAt(P,J):- timex(I), timex(J), I<J, 
               initiates(Q,P,I), 
               happens(Q, I),
               not clipped(I, P, J).
               
clipped(S, F, T) :- timex(S), timex(T),
                    S< R, R<T,
                              terminates(E, F, R),
                              happens(E, R).


%%%%%%%%%%%%%%%%%%%%%%
% Background Knowledge.
%%%%%%%%%%%%%%%%%%%%%%
event(add(G)):-sugar(G).
event(use(G)):-sugar(G).
fluent(available(G)):-sugar(G).

initiates(add(G),available(G), T):-sugar(G), timex(T). 
terminates(use(G),available(G), T):-sugar(G), timex(T). 

happens(add(lactose),0).
happens(add(glucose),0).


timex(0..9).

sugar(lactose).
sugar(glucose).

%happens(use(lactose), A) :-
%        \+holdsAt(available(glucose),A),
%        holdsAt(available(lactose), A).


:- happens(use(G),T), not holdsAt(available(G),T).

%%%%%%%%%%%%%%%%%%%%%
%examples
%%%%%%%%%%%%%%%%%%%%%
goal(examples).

examples :- 
holdsAt(available(lactose),1),
holdsAt(available(lactose),2),
not holdsAt(available(lactose),3).

%notholdsAt(X,Y):- not(holdsAt(X,Y)),sugar(X),timex(Y).
%timex(0..9).
