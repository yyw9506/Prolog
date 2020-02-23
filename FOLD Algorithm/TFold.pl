% Author: Xinyu Zhang, Yuyao Wang
% Date: 2019-11-22

:- import ord_add_element/3 from ordsets.
:- import concat_atom/3 from string.
:- dynamic ab/1.
:- dynamic predicates/1.
:- dynamic n_ab/1.
:- dynamic d/1.
%%%%%%%%%%%%%%%%%%%%%%%
% Basic functions
%%%%%%%%%%%%%%%%%%%%%%%
member(X,[X|_]).
member(X,[_|T]):-
	member(X,T).
	
append([], L, L).
append([H|T],M,[H|N]):-
	append(T,M,N).

len([],0).
len([_|L],N):-
	len(L,M),
	N is M+1.

delete(_, [], []).
delete(X, [X|T], R):-
	!,
	delete(X, T, R).
delete(X, [H|T], R):-
	delete(X, T, R1),
	R = [H|R1].

add_predicates(L):-
	asserta(predicates(L)).

n_ab(0).
add:-
	n_ab(X),
	X1 is X + 1,
	retract(n_ab(X)),
	asserta(n_ab(X1)).
%%%%%%%%%%%%%%%%%%%%%%%
% Minor functions
%%%%%%%%%%%%%%%%%%%%%%%
load_file(File):-
	load_dyn(File).
	
asserta_list([]).
asserta_list([H|T]):-
	asserta(H),
	asserta_list(T). 

retract_list([]).
retract_list([H|T]):-
	retract(H),
	retract_list(T). 

% return background list: [E1,E2,...]
get_background(Background):-
	%findall(E, background(E), Background).
	
	Background = [
			bird(a),
			bird(b),
			cat(c),
			penguin(d)
		].

add_goal(G):-
	asserta(G).
%%%%%%%%%%%%%%%%%%%%%%%
% Major functions
%%%%%%%%%%%%%%%%%%%%%%%

run() :-
	% Inputs
	Predicates = [bird, cat, fly, penguin],
	Pos = [a,b],
	Neg = [c,d],
	Goal = fly,
	add_goal(fly(_)),
	get_background(Background),
	(
		retract_list(Background) -> 
		writeln('database refreshed.'),
		asserta_list(Background);
		
		writeln('database established.'), 
		asserta_list(Background)
	),

	% run fold algorithm
	fold(Background, Pos, Neg, Predicates, Goal, false).

% D: default, Ab: abnormal, IsExcept: False/True
fold(Background, Pos, Neg , Predicates, Goal, IsExcept):-
	writeln(''),
	writeln('------------INPUTS------------'),
	writeln('Background:'),
	writeln(Background),
	writeln('------------------------------'),
	
	writeln('Positive Set:'),
	writeln(Pos),
	writeln('------------------------------'),
	
	writeln('Negative Set'),
	writeln(Neg),
	writeln('------------------------------'),

	writeln('Predicates:'),
	writeln(Predicates),
	writeln('------------------------------'),

	writeln('Goal:'),
	writeln(Goal),
	writeln('------------------------------'),
	add_predicates(Predicates),
	fold_loop(Goal, Pos, Neg, IsExcept, [], D1),
	ab(Y),
	writeln('Final Answer:'),
	writeln('D = '), 
	writeln(D1),
	writeln('AB = '),
	writeln(Y),
	writeln('-----------Check1-------------').


fold_loop(Goal, Pos, Neg, IsExcept, Prev, D):- 
	len(Pos, Len),
	(	
		Len > 0 ->
		% c ← (goal :- true.)
		Goal_Predicate =..[Goal, _],
		specialize(Pos, Neg, (Goal_Predicate:-true), PosClause1, true),
		uncovered(PosClause1, Pos, Pos1),
		write("Updated uncovered positive exampels: "), 
		writeln(Pos1),
		writeln(Goal_Predicate),
		(
			IsExcept ->
			true
			; append_d(PosClause1)
		),
		% cˆ ← specialize(c, E+, E−)
		% Clause = (Goal_Predicate:-true),
		%writeln(Clause),
		fold_loop(Goal, Pos1, Neg, IsExcept, [PosClause1|Prev], D)
		; Prev = D
		
	).

add_literal(Literal, (A :- L), (A :- NewL), IsPos):-
	Literal =..[P,_],
	A =..[_, X],
	Ltemp =..[P,X],
	(
		IsPos -> 
		Ls = Ltemp
		;Ls = (\+Ltemp)
	),
	(
		L = true ->
		NewL = Ls
		; NewL = (L, Ls)
	).


add_best_literal(Ls, Clause, Pos, Neg, CDef, IG):-
	getIGValue1(Clause, Pos, Neg, IG1),
	best_next_literal(Ls, Pos, Neg, Clause, IG1, -1, _, IG, CDef).

getIGValue1(Clause, Pos, Neg, IG):-
	writeln('before tuples'),
	writeln(Clause),
	writeln(Pos),
	writeln(Ptuples),
	tuples(Clause, Pos, Ptuples),
	writeln('after tuple'),
	len(Ptuples, PL),
	(
		PL =:= 0 ->
		IG = 0
		; tuples(Clause, Neg, Ntuples),
		len(Ntuples, NL),
		Temp is PL / (PL + NL),
		log(Temp, Temp1),
		IG is Temp1 * 1.442695
	).

tuples((_:-B), Xs, Tuples):-
	writeln('before clause_body_list'),
	clause_body_list(B, BodyList),
	check(BodyList, Xs, Tuples).

clause_body_list([],[]):- !.
clause_body_list(E, BodyList):-
	E == true ->
	clause_body_list([], BodyList)
	; E =.. [A, B|T],
	(
		A =',' ->
		(
			B = true ->
			[CRest] = T,
			clause_body_list(CRest, BodyList)
			; [CRest] = T,
			clause_body_list(CRest, BodyList1),
			BodyList = [B|BodyList1]
		)
		;(
			A = true ->
			clause_body_list([], BodyList)
			; (
				A = member ->
				[TBlock] = T,
				Body =.. [A, B, TBlock],
				clause_body_list([], BodyList1),
				BodyList = [Body|BodyList1]
				; Body =.. [A, B],
				clause_body_list([], BodyList1),
				BodyList = [Body|BodyList1]
			)
		)
	).

check(_,[],[]):- !.
check(BodyList, [H|T], Tuples):-
	(
		satisfy(BodyList, H) ->
		check(BodyList, T, Tuples1),
		Tuples = [H|Tuples1]
		; check(BodyList, T, Tuples)
	).

satisfy([], _).
satisfy([L|T], H):-
	L =.. [LName, _, H1],
	LName = member,
	C =.. [LName, H, H1],
	C,
	satisfy(T, H),
	!.
satisfy([L|T], H):-
	L =.. [LName, Body],
	(
		LName = (\+) ->
		Body =.. [LLName, _],
		C0 = [LLName, H],
		C = (\+C0)
		; C =.. [LName, H]
	),
	C,
	satisfy(T, H).

log_series_limit(99).  

log(0,0).
log(X,Y) :-
  X > 0,
  log_series_limit(L),
  log_e_series(X,1,Y,1,L).

log_e_series(_,_,0,Exp,Limit) :-
  Exp > Limit,
  !.

log_e_series(X,_,Y,1,Limit) :-
  !,
  Term1 is ((X-1)/(X+1)),
  Term2 is Term1 * 2,
  log_e_series(X,Term1,Y2,3,Limit),
  Y is Term2 + Y2.

log_e_series(X,Term,Y,Exp,Limit) :-
  Term1 is Term * ((X-1)/(X+1)) * ((X-1)/(X+1)),
  Term2 is Term1 * (2 / Exp),
  Exp2 is Exp + 2,
  log_e_series(X,Term1,Y2,Exp2,Limit),
  Y is Term2 + Y2.

best_next_literal([], _, _, _, _, Gain, Clause, Gain, Clause).
best_next_literal([L|Ls], Pos, Neg, Clause, IG, Gain0, Best0, Gain, Best):-
	writeln('next literal'),
	Literal =.. [L,_],
	add_literal(Literal, Clause, Best1, true),
	getIGValue(Neg, Pos, IG, Best1, Gain1),
	(
		Gain1 > Gain0 ->
		best_next_literal(Ls, Pos, Neg, Clause, IG, Gain1, Literal, Gain, Best)
		; (Gain1 =:= Gain0, Gain0 >= 0) ->
		tie_clause(Clause, Literal, Best0, Best2),
		best_next_literal(Ls, Pos, Neg, Clause, IG, Gain0, Best2, Gain, Best)
		; best_next_literal(Ls, Pos, Neg, Clause, IG, Gain0, Best0, Gain, Best)
	).

getIGValue(Neg, Pos, IG, BClause, Gain):-
	covered(BClause, Pos, Ret),
	len(Ret, LRe),
	(
		LRe =:= 0 ->
		Gain = -1
		; getIGValue1(BClause, Pos, Neg, IG1),
		Gain is LRe * (IG1 - IG)
	).

covered((A:-B), Xs, Xs1):-
	tuples((A:-B), Xs, Xs1).

tie_clause(Clause, B1, B2, Ret):-
	add_literal(B1, Clause, (_:Body1), true),
	add_literal(B2, Clause, (_:Body2), true),
	all_variables(Body1, V1),
	all_variables(Body2, V2),
	len(V1, L1),
	len(V2, L2),
	(
		L1 < L2 ->
		Ret = B1;
		Ret = B2
	).

all_variables(B, V):-
	all_variables(B, [], V).
all_variables(B, V0, V):-
	var(B),
	!,
	ord_add_element(V0, B, V).
all_variables(B, V0, V):-
	ground(B),
	!,
	V = V0.
all_variables(Term, V0, V):-
	functor(Term, _, N),
	variables_in_args(N, Term, V0, V).

variables_in_args(N, Term, V0, V):-
	(
		N =:= 0 ->
		V = V0
		; arg(N, Term, Arg),
		all_variables(Arg, V0, V1),
		N1 is N - 1,
		variables_in_args(N1, Term, V1, V)
	).

specialize(Pos, Neg, Clause, PosClause, Just_started):-
	writeln('before add best literal'),
	predicates(Ls),
	writeln(Ls),
	add_best_literal(Ls, Clause, Pos, Neg, CDef, IG),
	writeln('after add best literal'),
	(
		IG >= 0 ->
		add_literal(CDef, Clause, NewClause, true),
		delete_predicate(CDef)
		; (
			Just_started = true ->
			enumerate(Clause, Pos, NewClause)
			; exception(Clause, Neg, Pos, NewClause),
			(
				NewClause = [] ->
				enumerate(Clause, Pos, NewClause)
				; true
			)
		)
	),
	uncovered(NewClause, Pos, Pos1),
	covered(NewClause, Neg, Neg1),
	(
		Neg1 = [] ->
		PosClause = NewClause
		; specialize(Pos1, Neg1, NewClause, PosClause, flase)
	).
		
delete_predicate(H):-
	H =.. [Name, _],
	predicates(L),
	delete(Name, L, R),
	retract(predicates(_)),
	asserta(predicates(R)).

exception((Goal:-Body), Pos, Neg, Clause1):-
	predicates(Ls),
	add_best_literal(Ls, (Goal:-Body), Pos, Neg, _, IG),
	(
		IG >= 0 ->
		get_background(B),
		predicates(P),
		Goal =.. [GName,_],
		fold(GName, Pos, Neg, B, P, D_, _, true),
		n_ab(Current_n_ab),
		concat_atom([ab, Current_n_ab], '', C_abName),
		C_ab =.. [C_abName, _],
		add,
		append_rule_to_ab(D_, C_ab),
		add_literal(C_ab, (Goal:-Body), Clause1, false)
		; Clause1 = []
	).
	
append_rule_to_ab([], _).
append_rule_to_ab([PosC|Rest], C_ab):-
	PosC = (_:-Body),
	add_literal(Body, (C_ab:-true), C_hat, true),
	append_ab(C_hat),
	append_rule_to_ab(Rest, C_ab).

d([]).
append_d(X):-
	d(L),
	retract(d(_)),
	append(L, [X], L1),
	asserta(d(L1)).

ab([]).
append_ab(X):-
	ab(L),
	retract(ab(_)),
	append(L, [X], L1),
	asserta(ab(L1)),
	asserta(X).

enumerate(Clause0, [H|_], Clause1):-
	Clause0 = (C0Head:- C0Body),
	C0Head =.. [_, Arg],
	HLiteral =.. [member, Arg, [H]],
	(
		C0Body = true ->
		Clause1 = (C0Head:- HLiteral)
		; Clause1 = (C0Head:- (C0Body, HLiteral))
	).

uncovered((A:-B), Xs, Xs1):-
	tuples((A:-B), Xs, Xs0),
	uncover_h(Xs, Xs0, Xs1).
uncover_h([], _, []).
uncover_h([H|T], Xs0, Xs1):-
	(
		member(H, Xs0) ->
		uncover_h(T, Xs0, Xs1)
		; uncover_h(T, Xs0, Xs2),
		Xs1 = [H|Xs2]
	).
	
	
	
	

	
	

	
	
	