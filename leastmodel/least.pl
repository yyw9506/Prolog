% Yuyao Wang
% helper functions
append([], L, L).
append([H|T],M,[H|N]):-
	append(T,M,N).

member([X|_], X).
member([_|T], X):-
	member(T, X).
	
flatten(X,[X]):- \+ is_list(X).
flatten([],[]).
flatten([H|T],T1):-
	flatten(H, H1),
	flatten(T,T2),
	append(H1,T2,T1).

subset([], []).
subset([E|Tail], [E|NTail]):-
 	subset(Tail, NTail).
subset([_|Tail], NTail):-
 	subset(Tail, NTail).

% propositions
propositions(P,L):-
	% get all Propositions
	findall(Proposition, (member(P, rule(Proposition,_))), L1),
	% get all literals
	findall(Literals, (member(P, rule(_,Literals)), Literals\=[]), L2),
	flatten(L2,L3),
	append(L1,L3,FL),
	% sort and remove duplicates
	sort(FL,L).
	
% tp
tp(P,M1,M2):-
	findall(Proposition, (member(P, rule(Proposition,Literals)), subset(M1,Literals)), M),
	sort(M,M2).

tp_test(P,M1,M2):-
	tp_helper(P,M1,M),
	%writeln(M),
	sort(M,M2).

tp_helper([],_,[]).
tp_helper([rule(A,X)|T],M1,L):-
	subset(M1,X),
	tp_helper(T,M1,L2),
	append([A],L2,L).

tp_helper([rule(_,X)|T],M1,L):-
	\+ subset(M1,X),
	tp_helper(T,M1,L).
	
% leastmodel 
leastmodel(P,M):-
	leastmodel_helper(P,[],M).
	
leastmodel_helper(P,M1,M):-
	tp(P,M1,M2),
	(
		M1 \= M2
		-> leastmodel_helper(P,M2,M)
		; M = M2
	).