% Yuyao Wang
% load file
load_file(Path):-
	load_dyn(Path).

% helper functions
append([], L, L).
append([H|T],M,[H|N]):-
	append(T,M,N).

% find kth elemnt of a list
kth([X|_],X,1).
kth([_|T],X,K):-
	kth(T,X,N),
	K is N +1.

% length of a list
len([],0).
len([_|L],N):-
	len(L,M),
	N is M+1.

% sum of a list
sum([],0).
sum([H|T],Sum):-
	sum(T, Sub),
	Sum is Sub + H.

member(X,[X|_]).
member(X,[_|Y]):-
	member(X,Y).

remove_duplicates([],[]).
remove_duplicates([H|T], List) :-    
     member(H, T),
     remove_duplicates(T, List).
remove_duplicates([H|T], [H|T1]) :- 
      \+member(H, T),
      remove_duplicates(T, T1).

subset([], []).
subset([E|Tail], [E|NTail]):-
 	subset(Tail, NTail).
subset([_|Tail], NTail):-
 	subset(Tail, NTail).

pack([],[]).
pack([X|Xs],[Z|Zs]) :- transfer(X,Xs,Ys,Z), pack(Ys,Zs).
transfer(X,[],[],[X]).
transfer(X,[Y|Ys],[Y|Ys],[X]) :- X \= Y.
transfer(X,[X|Xs],Ys,[X|Zs]) :- transfer(X,Xs,Ys,Zs).

encode(L1,L2) :- 
	pack(L1,L), 
	transform(L,L2).
transform([],[]).
transform([[X|Xs]|Ys],[[N,X]|Zs]) :- 
	len([X|Xs],N), 
	transform(Ys,Zs).
	
flatten(X,[X]):- \+ is_list(X).
flatten([],[]).
flatten([H|T],T1):-
	flatten(H, H1),
	flatten(T,T2),
	append(H1,T2,T1).

checklimit([],_).
checklimit([H|T],Limit):-
	H =< Limit,
	checklimit(T,Limit).

% validate
validate(Limit,X):-
	findall([O],member([O,P],X),L1),
	flatten(L1,NL),
	encode(NL,NL1),
	findall(N,member([N,O],NL1),L2),
	checklimit(L2,Limit).
	
validated_offers([],[]).
validated_offers([H|T],Offers):-
	findall([O,P,A,U],(offer(O,P,A,U),member([O,P],H)),H1),
	validated_offers(T,Acc),
	append([H1],Acc,Offers).

validate_activity([],_,[]).
validate_activity([H|T],NeedList,RelatedOffers):-
	findall([A,U],(member([A,_],NeedList),member([O,P,A,U],H)),H1),
	validate_activity(T,NeedList,Acc),
	append([H1],Acc,RelatedOffers).	

%validate_units_helper(C,Need)
validate_units_helper(_,[],[]).
validate_units_helper(C, [[A,U1]|T], Units):-
	findall(U,member([A,U],C),Unit),
	validate_units_helper(C, T, Acc),
	% sum of the units of offers
	sum(Unit,Value),
	append([[A,Value]],Acc,Units).

validate_units([],_,[]).
validate_units([H|T],NeedList,UnitsList):-
	validate_units_helper(H,NeedList,Units),
	%writeln(Units),
	validate_units(T,NeedList,Acc),
	append([Units],Acc,UnitsList).
	
packlist(List,NList,Limit):-
	findall(X,(subset(List,X),validate(Limit,X)),NList).
	
findvalidate([],_,[]).
findvalidate([H|T],NeedList,[ValList|T1]):-
	findall([A,U],(member([A,U],H),member([A,U1],NeedList),U>=U1),ValList),
	len(NeedList,NL),
	%writeln(NL),
	len(ValList,VL),
	%writeln(VL),
	VL=:=NL ->
	writeln('valid!'),
	findvalidate(T,NeedList,T1).

findvalidate([H|T],NeedList,T2):-
	findall([A,U],(member([A,U],H),member([A,U1],NeedList),U>=U1),ValList),
	len(NeedList,NL),
	%writeln(NL),
	len(ValList,VL),
	%writeln(VL),
	\+ VL=:=NL ->
	writeln('not valid!'),
	findvalidate(T,NeedList,T2).

findprice([],_,_,[]).
findprice([H|T],UnitsList,CanList,[Total|T1]):-
	kth(UnitsList,H,K),
	kth(CanList,OP,K),
	findall(Price,(member([O,P],OP),price(O,P,Price)),PriceList),
	sum(PriceList,Total),
	findprice(T,UnitsList,CanList,T1).
	
totalcost(X):-
	maxacceptedoffer(Limit), 
	write('Number of packets in each operator:'),
	writeln(Limit),
	findall([O,P],(offer(O,P,A,U)),List),
	remove_duplicates(List,NewList),
	packlist(NewList,CanList,Limit),!,
	writeln('*Candidate solutions [O,P].'),
	writeln(CanList),
	len(CanList, CanLen),
	write('*Number of candidate solution:'),
	writeln(CanLen),
	findall([A,U],(need(A,U)),NeedList),
	validated_offers(CanList,OfferList),
	%writeln(OfferList),
	validate_activity(OfferList,NeedList,RelatedOffers),
	%writeln(RelatedOffers),
	validate_units(RelatedOffers,NeedList,UnitsList),
	writeln('*[A,U] of each candidate:'),
	writeln(UnitsList),
	len(UnitsList,UniLen),
	write('-Validating '),
	write(UniLen),
	writeln(' candidate solutions....'),
	findvalidate(UnitsList,NeedList,Result),
	%writeln('---------check point------------'),
	writeln('Requirement for Activity and Units .'),
	writeln(NeedList),
	writeln('Valid Aacivity & Units.'),
	writeln(Result), 
	len(Result,Rnum),
	write('Number of valid solution:'),
	writeln(Rnum),
	(
		Rnum =:= 0 -> 
			writeln('No solution!'),fail;
			
		Rnum =:= 1 ->
		Result = [AU|_],
		kth(UnitsList,AU,K),
		kth(CanList,OP,K),
		writeln('[O,P] Operator & Package of accepted offers:'),
		writeln(OP),
		findall(Price,(member([O,P],OP),price(O,P,Price)),PriceList),
		write('X (Price) = '),
		sum(PriceList,X),
		writeln(X);
		
		Rnum > 1,
		findprice(Result,UnitsList,CanList,PriceList1),
		sort(PriceList1,[Min|_]),
		kth(PriceList1,Min,K1),
		kth(Result,AU1,K1),
		kth(UnitsList,AU1,K2),
		kth(CanList,OP1,K2),
		writeln('[O,P] Operator & Package of accepted offers:'),
		writeln(OP1),
		X = Min,
		write('X (Price) = '),
		writeln(X)
	).
		
		
	
	
	