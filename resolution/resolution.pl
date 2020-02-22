% Yuyao Wang
% helper functions
len([],0).
len([_|L],N):-
	len(L,M),
	N is M+1.

member([X|_], X).
member([_|T], X):-
	member(T, X).

append([],Acc,Acc).
append([H|T],Acc,[H|L]):-
	append(T,Acc,L).

delete([X|T],X,T).
delete([H|T],X,[H|L1]):-
	delete(T,X,L1).

% major functions
set([],[]).
set([X|T],[X|H]):-
	set(T,E),
	(
		member(E,X) ->
		delete(E,X,H);
		H=E
	).

% transfrom the format of clauses
getClause(or(X,Y),L):-
	getClause(X,L1),
	getClause(Y,L2),
	append(L1,L2,L),!.
	
getClause(X,[X]).

getAnswer(C, ANS, ANS):-
	member(C, [_,[]]),!.
	
% get answer using resolution
getAnswer(C, TMP, ANS):-
	member(C,[CID1,C1]),
	%writeln('--------'),
	member(C,[CID2,C2]),
	CID1=\=CID2,
	delete(C1,T1,NewC1),
	delete(C2, neg(T1),NewC2),
	append(NewC1,NewC2,NewC),
	%writeln('----------'),
	%writeln(NewC),
	set(NewC,SetNewC),
	%writeln(SetNewC),
	%writeln('----------'),
	len(C, N), NewCID is N+1,
	\+ member(C,[_,SetNewC]),
	getAnswer([[NewCID,SetNewC]|C], [[CID1,CID2,SetNewC,NewCID]|TMP], ANS).

printAns([]).
printAns([[CID1, CID2, NewC, NewCID]|T]):-
	printAns(T),
	write('resolution('),
	write(CID1),
	write(', '),
	write(CID2),
	write(', '),
	toDisjunction(NewC,Disjunction),
	write(Disjunction),
	write(', '),write(NewCID),writeln(').').

toDisjunction([],'empty'):-!.
toDisjunction([X],X):-!.
toDisjunction([X|T],or(NT,X)):- toDisjunction(T,NT),!.

% main: resolution
resolution(InputFile):-
	load_dyn(InputFile),
	%get myClause() and myQuery()
	findall([N,Z], (myClause(N,Y), getClause(Y,Z)), C),
	findall([N,[neg(Y)]], myQuery(N,Y), QC),
	writeln('--------------------'),
	writeln(C),
	%writeln(QC),
	%----------------------cs
	%len(C,N),
	%M is N + 1,
	%QC = [[M,[neg(Q)]]],
	%writeln(QC),
	%----------------------
	append(C,QC,All),
	% append myClause() and myQuery()
	%swriteln(All),
	(	
		% get answer using resolution rules
		getAnswer(All,[],ANS) ->
		writeln('resolution(success).'),
		%writeln(ANS),
		printAns(ANS);
		writeln('resolution(fail).')
	).