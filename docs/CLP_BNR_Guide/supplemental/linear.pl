%
% rewrite_linear/3 takes a list of constraint equations and divides into a list of
%	linear constraints and a list of others. It then translates the linear equations into
%	an equivalent set of equations after performing Gaussian elimination. 
%
rewrite_linear(EQs,LinEQs,Others) :-
	term_variables(EQs,Vars),              % collect all Var's
	% process linear equations into A matrix and B vector (constants)
	build_As_Bs(EQs,Vars,As,Bs,Others),
	% perform Gaussian elimination
	triangular(As,Bs,TAs,TBs),
	% reconstruct equations => LinEQs
	build_elim(TAs,Vars,TBs,LinEQs).

% build coefficent matrix A and constants vector B
build_As_Bs([],_,[],[],[]).
build_As_Bs([EQ|EQs],Vars,[A|As],[B|Bs],Others):-
	normal_form(EQ, NEx),
	exp_terms(NEx,P/P,Terms/[]),
	build_A_B(Vars,Terms,A,B), !,
	build_As_Bs(EQs,Vars,As,Bs,Others).
build_As_Bs([EQ|EQs],Vars,As,Bs,[EQ|Others]) :-  % failed linearity checks, put in Others
	build_As_Bs(EQs,Vars,As,Bs,Others).

% convert equations to LHS expression
normal_form(E1==Zero, E1)  :- Zero==0, !.
normal_form(Zero==E2, E2)  :- Zero==0, !.
normal_form(E1==E2, E1-E2).

% convert exression to a list of +/- terms
exp_terms(V, Terms/[V|NewT], Terms/NewT) :- var(V),!.
exp_terms(A+B, Terms, NewTerms) :- !,
	exp_terms(A, Terms, ATerms),
	exp_terms(B, ATerms, NewTerms).
exp_terms(A-B, Terms, NewTerms) :- !,
	exp_terms(A, Terms, ATerms),
	exp_terms(-B, ATerms, NewTerms).
exp_terms(-A, Terms/NAts, Terms/NewT) :- !,
	exp_terms(A, P/P, Ats/NewT),
	negate_terms(Ats/NewT, NAts/NewT).
exp_terms(Exp, Terms/[Exp|NewT], Terms/NewT).


negate_terms(T/Tail, T/Tail) :- T==Tail, !.
negate_terms([A|As]/Tail, [-A|NAs]/Tail) :-
	negate_terms(As/Tail, NAs/Tail).
	
build_A_B([],Terms,[],B) :-
	eval_terms(Terms,0,B1),
	B is -B1.
build_A_B([V|Vars],Terms,[A|As],B) :-
	eval_terms(Terms,V,A),
	build_A_B(Vars,Terms,As,B).
	
eval_terms([],_,0).
eval_terms([T|Terms],V,A) :-            % V is in T
	term_variables(T,[V1]), V==V1, !,   % must be only variable
	term_singletons(T,Ss), Ss=[V], !,   % singleton V is in T (Extra check required due to SWIP bug)
	copy_term_nat(T,Tc),                % copy without attributes
	eval_exp(Tc,N1),
	eval_terms(Terms,V,N2),
	A is N1+N2.
eval_terms([T|Terms],V,A) :- 
	var(V), !,                          % V not in T
	term_variables(T,TVs), length(TVs,L), L=<1,   % 0 (ground) or 1 variable, ...
	term_singletons(T,TSs), TSs==TVs,   % must be singleton (linear check)
	eval_terms(Terms,V,A).
eval_terms([T|Terms],0,B) :-            % collecting ground terms
	(ground(T) -> N1 is T ; N1=0),
	eval_terms(Terms,0,N2),
	B is N1+N2.
	
% evaluate - note only */ and unary - allowed.
eval_exp(T,1) :- var(T), !.  % single occurance of var, substitute 1
eval_exp(-A,E) :- !, eval_exp(A,Ae), E is -Ae.
eval_exp(A*B,E) :- !, eval_exp(A,Ae), eval_exp(B,Be), E is Ae*Be.
%%%eval_exp(A/B,E) :- rational(A), rational(B), !, E is A rdiv B.
eval_exp(A/B,E) :- !, eval_exp(A,Ae), eval_exp(B,Be), E is Ae/Be.
eval_exp(T,E) :- ground(T), !, E is T.


% perform Gaussian elimination on A's (rows) and B's (constants)
triangular([],_,[],[]) :- !.                              % no rows left
triangular([[A]|As],[B|Bs],[[A]|As],[B|Bs]) :-  A=:=0,!,  % last column with 0
	B=:=0.
triangular([[A]|As],[B|Bs],[NPA|NAs],[NPB|NBs]) :-  !,    % last column
	normalize_pivot([A],B,NPA,NPB),
	apply_pivot(As,Bs,NPA,NPB,NAs,NBs).
triangular(As,Bs,[NPA|TAs],[NPB|TBs]) :-
	pivot_row(As,Bs,PA,PB,RAs,RBs), !,
	normalize_pivot(PA,PB,NPA,NPB),
	apply_pivot(RAs,RBs,NPA,NPB,NAs,NBs),
	triangular(NAs,NBs,TAs,TBs).
triangular(As,Bs,TAs,TBs) :- % no pivot row for next var
	remove_zero_column(As,NAs),
	triangular(NAs,Bs,TAs,TBs).

remove_zero_column([],[]).
remove_zero_column([[_|As]|Rows],[As|NRows]) :-
	remove_zero_column(Rows,NRows).

% select a pivot row from As and Bs and return remaining, fails if no pivot found 
pivot_row([A|As],[B|Bs],A,B,As,Bs) :-
	A=[A1|_], A1=\=0, !.
pivot_row([A|As],[B|Bs],PA,PB,[A|RAs],[B|RBs]) :-
	pivot_row(As,Bs,PA,PB,RAs,RBs).

% normalize pivot row
normalize_pivot([A1|As],B,[1|NAs],NB) :-
	normalize_pivot(As,A1,NAs),
	NB is B/A1.
	
normalize_pivot([],_,[]).
normalize_pivot([A|As],A1,[NA|NAs]) :-
	NA is A/A1,
	normalize_pivot(As,A1,NAs).

% apply pivot to remaining rows
apply_pivot([],_,_,_,[],[]).                                             % no rows
apply_pivot([[A]|Rows],[B|Bs],[1|NA],NB,[[0]|PRows],[B|PBs]) :- A=:=0, !, B=:=0,  % 0 row (B should also be 0)
	apply_pivot(Rows,Bs,[1|NA],NB,PRows,PBs).
apply_pivot([[A1|Row]|Rows],[B|Bs],[1|NA],NB,[PRow|PRows],[PB|PBs]) :-
	apply_pivot(Row,A1,NA,PRow),
	PB is B-A1*NB,
	apply_pivot(Rows,Bs,[1|NA],NB,PRows,PBs).

apply_pivot([],_,[],[]).
apply_pivot([A|As],A1,[NA|NAs],[PA|PAs]) :-
	PA is A-A1*NA,
	apply_pivot(As,A1,NAs,PAs).

% build constraint expression list: A_matrix x V_vector = B_vector
build_elim([],_,_,[]) :- !.  % ran out of rows
build_elim([[A]|Rows],Vars,[_|Bs],Cs) :- A=:=0, !,   % zero row, skip it
	build_elim(Rows,Vars,Bs,Cs).
build_elim([[A]],[V],[B],[Vlhs==B]) :- !, 
	mult_term(A,V,0,Exp),
	Exp=..[Op,0,Vexp],
	(Op='-' -> Vlhs= -Vexp ; Vlhs=Vexp).
build_elim([[1|As]|Rows],Vars,[B|Bs],[CE==B|Cs]) :-
	length(As,RLen1),length(Vars,VLen),
	trim_vars(Vars,VLen,RLen1,[V|TVars]),
	constraint_exp(As,TVars,V,CE),
	build_elim(Rows,TVars,Bs,Cs).

trim_vars(Vars,VLen,RLen,Vars) :-
	VLen =:= RLen+1, !.
trim_vars([_|Vars],VLen,RLen,TVars) :-
	NVLen is VLen-1,
	trim_vars(Vars,NVLen,RLen,TVars).

constraint_exp([],[],Exp,Exp).
constraint_exp([A|As],[V|Vars],In,Out) :-
	mult_term(A,V,In,Exp),
	constraint_exp(As,Vars,Exp,Out).

mult_term(A,_,In,In) :- A=:=0, !.
mult_term(1,V,In,In+V) :-!.
mult_term(-1,V,In,In-V) :-!.
mult_term(A,V,In,In+A*V) :- A>0, !.
mult_term(A,V,In,In-MA*V) :- !, MA is -A.
