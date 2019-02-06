%
% Expression variables are Prolog var's; numeric constants are precise.
% Note floats are treated like variables and no arithmetic is performed on them
%
constant_(C) :- rational(C).  % (integers or rationals)

% works for print and listener but may be misleading
% user:portray(M rdiv N) :- print(M/N).

% used for sorting expressions and terms.
sort_exp_(List, Sorted) :- sort(0, @=<, List, Sorted).

% negatable operators
negate_op_(+,-).
negate_op_(-,+).

% power operators
invert_op_(*,/).
invert_op_(/,*).

% signed multiplier and power values
sign_val_(+,C,C) :- C>=0.
sign_val_(-,C,N) :- N is -C.

pwr_val_(*,C,C) :- C>=0.
pwr_val_(/,C,N) :- N is -C.

equality_op_(==).
equality_op_(<>).
equality_op_(=<).
equality_op_(>=).
equality_op_(<).
equality_op_(>).

% utility to distribute A*(B1+B2) if they have variables in common or A is a constant
distribute_(C,B,Exp) :-
	constant_(C), !,
	negate_op_(AddOp,_), B=..[AddOp,B1,B2],  % watch out for vars
	DExp=..[AddOp,C*B1,C*B2],
	simplify(DExp,Exp).
distribute_(A,B,Exp) :-
	negate_op_(AddOp,_), B=..[AddOp,B1,B2],  % watch out for vars
	shared_vars_(A,B),  % any shared vars
	!,
	DExp=..[AddOp,A*B1,A*B2],
	simplify(DExp,Exp).

% utility for (in)equality reduction 
normalize_(A,B,Op,ROp,Exp) :-
	rational(B,0,_), !,           % RHS = 0
	n_build_(Op, A, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	rational(A,0,_), !,           % LHS = 0
	n_build_(ROp, B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	occurs_in_(A,B), !,           % RHS is shared var
	n_build_(Op, A-B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	occurs_in_(B,A), !,           % LHS is shared var
	n_build_(ROp, B-A, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	compound(A), compound(B),     % LHS and RHS are expressions with shared vars
	shared_vars_(A,B), !,
	n_build_(Op, A-B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-     % everything else, leave LHS and RHS alone
	simplify(B,RHS),
	n_build_(Op, A, RHS, Exp).

occurs_in_(Exp, V) :- var(V), term_variables(Exp,Vs), shared_var_(Vs,V).

n_build_(Op, L, RHS, Exp) :- simplify(L,LHS), Exp=..[Op,LHS,RHS].

shared_vars_(A,B) :-
	term_variables(A,AVs),
	term_variables(B,BVs),
	shared_vars_in_(AVs,BVs).

shared_vars_in_([AV|_AVs],BVs) :-
	shared_var_(BVs,AV), !.
shared_vars_in_([_AV|AVs],BVs) :-
	shared_vars_in_(AVs,BVs).

shared_var_([BV|_BVs],AV) :-
	AV == BV, !.
shared_var_([_BV|BVs],AV) :-
	shared_var_(BVs,AV).


%
% simplify/2
%
simplify(A,A) :- var(A),!.

simplify(C,C) :- rational(C),!.  % includes integers

% possible distribute
simplify(A*B,Exp) :-
	compound(B),
	distribute_(A,B,Exp), !.
simplify(A*B,Exp) :-
	compound(A),
	distribute_(B,A,Exp), !.

% simplify equalities and inequalities
simplify(A==B,Exp) :-
	normalize_(A,B,==,==,Exp), !.

simplify(A=<B,Exp) :-
	normalize_(A,B,=<,>=,Exp), !.

simplify(A>=B,Exp) :-
	normalize_(A,B,>=,=<,Exp), !.

simplify(A<B,Exp) :-
	normalize_(A,B,<,>,Exp), !.

simplify(A>B,Exp) :-
	normalize_(A,B,>,<,Exp), !.

% simplify "cascaded" divisions
simplify(A/B,Exp) :- 
	compound(B), B=Bn/Bd, !,
	simplify(A*Bd/Bn,Exp).

%
% General purpose simplify
%
simplify(E,Exp) :-
	collect_exp_(E, L/L, Es/[]),  % collect terms in a difference list
	collect_exp_items(Es,Is),     % collect like terms
	reduce_exp_items_(Is,Exp),    % and reduce back to expression
	!.
	
collect_exp_(A, List/[term(+,A,1)|NewT], List/NewT) :-
	var(A), !.
	
collect_exp_(C, List/[C|NewT], List/NewT) :-
	rational(C), !.

collect_exp_(A, List/[term(Op,F,1)|NewT], List/NewT) :-    % floats as terms, can collect but not do arithmetic
	float(A), !,
	(A<0 -> Op = - ; Op = +),
	F is abs(A).

collect_exp_(N*A, List/[Term|NewT], List/NewT) :-  % user written terms
	mul_term_(N,A,Term), !.

collect_exp_(A*N, List/[Term|NewT], List/NewT) :-  % user written terms
	mul_term_(N,A,Term), !.

collect_exp_(-A,List/T, List/NewT) :-
	simplify(A,AT), collect_exp_(AT,P/P,ListA),
	negate_exp_(ListA,T/NewT).

collect_exp_(A-B,List,NewList) :-
	simplify(A,AT), collect_exp_(AT,List,ListA),
	collect_exp_(-B,ListA,NewList).
	
collect_exp_(A+B, List, NewList) :-
	simplify(A,AT), collect_exp_(AT,List,ListA),
	simplify(B,BT), collect_exp_(BT,ListA,NewList).

collect_exp_(T, List/[Term|NewT], List/NewT) :-
	simplify_term(T,Term).

mul_term_(N,A,Term) :-
	simplify(N,NT), constant_(NT),
	simplify(A,AT),
	(constant_(AT) -> Term is AT*NT ; (sign_val_(Op,NT,M), Term = term(Op,AT,M))).
	
negate_exp_(T/T,NewT/NewT) :- var(T).
negate_exp_([term(Op,V,N)|Es]/T,[term(NOp,V,N)|NEs]/NewT) :- !,
	negate_op_(Op,NOp),
	negate_exp_(Es/T,NEs/NewT).
negate_exp_([C|Es]/T,[NC|NEs]/NewT) :-
	constant_(C), NC is -C,
	negate_exp_(Es/T,NEs/NewT).

collect_exp_items([],[]).
collect_exp_items([E|Es],[NE|NEs]) :-
	collect_exp_item_(Es,E,NE,ENxt),
	collect_exp_items(ENxt,NEs).

collect_exp_item_([],E,E,[]).
collect_exp_item_([V|Es],U,Eo,EsNxt) :-
	constant_(U), constant_(V),  % constant values must be precise to add
	S is U+V,
	collect_exp_item_(Es,S,Eo,EsNxt).
collect_exp_item_([term(Op1,V,N1)|Es],term(Op2,U,N2),Eo,EsNxt) :-
	V==U, catch(abs(V) =\= inf,_,true), !,  % if V==U = infinity, fail to next choice.
	sign_val_(Op1,N1,S1), sign_val_(Op2,N2,S2),
	S is S1+S2,
	sign_val_(Op,S,N),
	collect_exp_item_(Es,term(Op,V,N),Eo,EsNxt).
collect_exp_item_([term(Op1,V,N1)|Es],term(Op2,U,N2),Eo,EsNxt) :-
	atomic(V), atomic(U), abs(V) =:= inf, abs(U) =:= inf,
	throw(error("Arithmetic operations not allowed on two infinities.")).
collect_exp_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-  % Note that imprecise floats are not added
	collect_exp_item_(Es,E,Eo,EsNxt).


reduce_exp_items_([],0).
reduce_exp_items_([T],Exp) :-
	reduce_exp_item_(T,Exp,_,_).
reduce_exp_items_([T1,T2|Ts],Exp) :-
	reduce_exp_item_(T1,Exp1,_,_),
	reduce_exp_item_(T2,_,Op,Exp2),
	build_exp_(Exp1,Exp2,Op,ExpN), !,  % ExpN =.. [Op,Exp1,Exp2], !,
	reduce_exp_items_([ExpN|Ts],Exp).

% throws away zeros
build_exp_(Zero,Exp2,-,NExp2) :- Zero == 0, build_Nexp_(Exp2, NExp2).
build_exp_(Zero,Exp2,+,Exp2)  :- Zero == 0.
build_exp_(Exp1,Zero,_,Exp1)  :- Zero == 0.
build_exp_(Exp1,Exp2,Op,ExpN) :- ExpN =.. [Op,Exp1,Exp2].

build_Nexp_(  V,   -V) :- var(V).
build_Nexp_(Exp, NExp) :- constant_(Exp), NExp is -Exp.
build_Nexp_(N*T, NN*T) :- constant_(N), NN is -N.
build_Nexp_(N/T, NN/T) :- constant_(N), NN is -N.
build_Nexp_(Exp, -Exp).

reduce_exp_item_(          V,   V, +,   V) :- var(V).
reduce_exp_item_(term(O,V,N),   S, O,   T) :- reduce_term_(V,N,O,T,S).
reduce_exp_item_(          R,   R, -,   M) :- constant_(R), R<0, M is -R.  % negative constants
reduce_exp_item_(          T,   T, +,   T).              % positive constants and anything else (?) 

% Case 1: _ * 0.
reduce_term_(_,0,+,0,0).
% Case 2: var * constant
reduce_term_(V,1,+,V, V) :- var(V).
reduce_term_(V,1,-,V,-V) :- var(V).
reduce_term_(V,N,+,N*V,N*V) :- var(V).
reduce_term_(V,N,-,N*V,M*V) :- var(V), M is -N.
% Case 3: (mul and div) * constant - need to find the beginning
reduce_term_(V1*V2,N,Op,T*V2,S*V2) :- reduce_term_(V1,N,Op,T,S).
reduce_term_(V1/V2,N,Op,T/V2,S/V2) :- reduce_term_(V1,N,Op,T,S).
% Case 4: constant * constant
reduce_term_(C,N,+,T,T)  :- constant_(C), T is C*N.
reduce_term_(C,N,-,T,S)  :- constant_(C), T is C*N, S is -T.
% Case 5: constant * float (Open question - should eval be deferred due to possible rounding error?)
reduce_term_(F,N,Op,T,S) :- float(F), abs(F)=:=inf, T is copysign(inf,sign(F)*sign(N)), (Op= + -> S=T ; S is -T).
reduce_term_(F,N,+,T,T)  :- float(F), T is F*N.
reduce_term_(F,N,-,T,S)  :- float(F), T is F*N, S is -T.
% Case 6: anything_else * constant
reduce_term_(V,1,+,V, V).
reduce_term_(V,1,-,V, -V).
reduce_term_(V,N,+,N*V, N*V).
reduce_term_(V,N,-,N*V, M*V) :- M is -N.

%
% simplify a term to an "expression" of term structures and constants
%
simplify_term(T,Term) :-
	collect_term_(T, L/L, Ts/[]),    % collect in a difference list
	collect_term_items_([1|Ts],Is),  % ensure there's a constant multiplier and collect like terms
	sort_exp_(Is,[C|SIs]),           % multiplier will be first, all others sorted
	reduce_term_items_(SIs,ITerm),   % reduce back to expression
	% this does constant folding if reduction resulted in a constant
	(constant_(ITerm) -> Term is ITerm*C ; (sign_val_(Op,C,M), Term = term(Op,ITerm,M))),
	!.

collect_term_(A, List/[elem(*,A,1)|NewT], List/NewT) :-
	var(A), !.
	
collect_term_(A, List/[A|NewT], List/NewT) :-
	rational(A), !.

collect_term_(A, List/[elem(*,A,1)|NewT], List/NewT) :-
	float(A), !.

collect_term_(-A, List, ListA/NewT) :- % -Term as Term * -1 for reducing signs
	simplify(A,AT), collect_term_(AT,List,ListA/[-1|NewT]).

collect_term_(A**N, List/[Term|NewT], List/NewT) :-  % possible special case of user written element
	simplify(N,NT), constant_(NT),
	simplify(A,AT),
	(constant_(AT) -> Term is AT**NT ; (pwr_val_(Op,NT,P), Term = elem(Op,AT,P))).

collect_term_(A*B,List,NewList) :-
	simplify(A,AT),	simplify(B,BT),
	collect_term_(AT,List,ListA),
	collect_term_(BT,ListA,NewList).
	
collect_term_(A/B,List,NewList) :-
	simplify(A,AT),	simplify(B,BT),
	collect_div_(AT,BT,List,NewList).

collect_term_(E,List/[elem(*,Exp,1)|NewT], List/NewT) :-
	E =.. [F|IArgs],
	simplify_list_(IArgs,OArgs),
	Exp =.. [F|OArgs].

simplify_list_([],[]).
simplify_list_([I|IArgs],[O|OArgs]) :-
	simplify(I,O),
	simplify_list_(IArgs,OArgs).

collect_div_(AT,BT,List/[N|NewT], List/NewT) :-
	constant_(AT),constant_(BT),
	(BT==0 -> throw(error("Zero divisor in constraint expression":AT/BT)) ; true),  % throw exception if BT=0
	N is AT rdiv BT.  % rational constant expressed as AT/BT
collect_div_(AT,BT,List,ListA/NewT) :-
	collect_term_(AT,List,ListA/T),
	collect_term_(BT,P/P,ListB),
	invert_term_(ListB,T/NewT).
	
invert_term_(T/T,NewT/NewT) :- var(T).
invert_term_([elem(Op,V,N)|Es]/T,[elem(IOp,V,N)|NEs]/NewT) :-
	(V==0.0 -> throw(error("Zero divisor in constraint expression":'_'/V)) ; true),  % throw exception if V=0.0
	invert_op_(Op,IOp),  %% NN is -N,
	invert_term_(Es/T,NEs/NewT).
invert_term_([N|Es]/T,[NN|NEs]/NewT) :-
	rational(N,A,B),  % constants
	(A==0 -> throw(error("Zero divisor in constraint expression":N)) ; true),       % throw exception if A=0
	NN is B rdiv A,
	invert_term_(Es/T,NEs/NewT).
	
collect_term_items_([],[]).
collect_term_items_([E|Es],[NE|NEs]) :-
	collect_term_item_(Es,E,NE,ENxt),
	collect_term_items_(ENxt,NEs).

collect_term_item_([],E,E,[]).
collect_term_item_([V|Es],U,Eo,EsNxt) :-
	constant_(U), constant_(V),  % precise for multiply
	S is U*V,
	collect_term_item_(Es,S,Eo,EsNxt).
collect_term_item_([elem(Op1,V,N1)|Es],elem(Op2,U,N2),Eo,EsNxt) :-
	V==U, catch(abs(V) =\= inf,_,true), !,  % if V==U = infinity, fail to next choice.
	pwr_val_(Op1,N1,S1), pwr_val_(Op2,N2,S2),
	S is S1+S2,
	pwr_val_(Op,S,N),
	collect_term_item_(Es,elem(Op,V,N),Eo,EsNxt).
collect_term_item_([elem(Op1,V,N1)|Es],elem(Op2,U,N2),Eo,EsNxt) :-
	atomic(V), atomic(U), abs(V) =:= inf, abs(U) =:= inf,
	throw(error("Arithmetic operations not allowed on two infinities.")).
collect_term_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-
	collect_term_item_(Es,E,Eo,EsNxt).

reduce_term_items_([0|_],0).    % element is 0 => 0
reduce_term_items_([T],Exp) :-  %%%% guaranteed to have at least one item
	reduce_term_item_(T,E,Op),
	build_term_(1,E,Op,Exp).  %% (Op = / -> Exp=1/E ; Exp=E).
reduce_term_items_([T1,T2|Ts],Exp) :-
	reduce_term_item_(T1,Exp1,_),
	reduce_term_item_(T2,Exp2,Op),
	build_term_(Exp1,Exp2,Op,ExpN),  %% ExpN =.. [Op,Exp1,Exp2],
	!,
	reduce_term_items_([ExpN|Ts],Exp).

build_term_( One, Exp, *, Exp) :- One==1.
build_term_( One, Exp, /,IExp) :- One==1, (rational(Exp,M,N) -> IExp is N rdiv M ; IExp = 1/Exp).
build_term_( Exp, One, _, Exp) :- One==1.
build_term_(Exp1,Exp2,Op, Exp) :- Exp =.. [Op,Exp1,Exp2].

reduce_term_item_(elem( _,_,0),    1,  *).
reduce_term_item_(elem(Op,V,1),    V, Op).
reduce_term_item_(elem(Op,V,E), V**E, Op).
reduce_term_item_(           R,    R,  *).  % catchall?? presumably a constant
