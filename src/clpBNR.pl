%
% CLP(BNR) == Constraints On Boolean, Integer, and Real Intervals
%
:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfx, ::),
	(::)/2,                % declare interval
	{}/1,                  % define constraint
	interval/1,            % filter for clpBNR constrained var
	numeric/1,             % filter for numeric Prolog terms: (integer;float;rational)
	list/1,                % for compatibility
	domain/2, range/2,     % for compatibility
	lower_bound/1,         % narrow interval to point equal to lower bound
	upper_bound/1,         % narrow interval to point equal to upper bound

	% additional constraint operators
	op(200, fy, ~),        % boolean 'not'
	op(500, yfx, and),     % boolean 'and'
	op(500, yfx, or),      % boolean 'or'
	op(500, yfx, nand),    % boolean 'nand'
	op(500, yfx, nor),     % boolean 'nor'
	op(500, yfx, xor),     % boolean 'xor'
	op(700, xfx, <>),      % integer not equal
	op(700, xfx, <=),      % set inclusion
	op(700, xfx, =>),      % set inclusion

	% utilities
	print_interval/1,      % print interval as list of two numbers (for compatability)
	solve/1, solve/2,      % solve (list of) intervals using split to find point solutions
	splitsolve/1, splitsolve/2,   % solve (list of) intervals using split
	absolve/1, absolve/2,  % absolve (list of) intervals, narrows by nibbling bounds
	minimize/3,            % minimize interval using user defined Solver
	maximize/3,            % maximize interval using user defined Solver
	enumerate/1,           % "enumerate" integers
	simplify/2,            % general purpose predicate for simplifying expressions of variables
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1        % get all defined in a list
	]).

	
/* missing(?) functionality:

1. arithmetic functions on intervals (delta, median, midpoint). Requires hooking is/2.
	
2. utility accumulate/2.

*/

/* supported interval relations:

+	-	*	/	**                    %% arithmetic
**                                    %% includes real exponent, odd/even integer
abs                                   %% absolute value
sqrt                                  %% square root (needed?)
min	max                               %% binary min/max
==	is	<>	=<	>=	<	>             %% comparison
<=	=>                                %% inclusion
and	or	nand	nor	xor	->            %% boolean
-	~                                 %% unary negate and not
exp	log                               %% exp/ln
sin	asin	cos	acos	tan	atan      %% trig functions

*/

:- style_check([-singleton, -discontiguous]).

%
% list(X) for compatability
%
list(X) :- is_list(X).

% numeric test (number or rational)
%
numeric(C) :- number(C), !.
numeric(C) :- rational(C).

:- include(ia_primitives).  % interval arithmetic relations via evalNode/4.

%
% Intervals are constrained (attributed) variables.
%
% Current interval bounds updates via setarg(Val) which is backtrackable
%

interval_object(Int, Type, Val, Nodelist) :-
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist)).       %%SWIP

% get current value
getValue(Num, Val) :-
	number(Num), !,         % floats and integers
	Val=[Num,Num].
getValue(Int, Val) :-       % an interval, get value from attribute
	get_attr(Int, clpBNR, interval(_, Val, _)), !.     %% optimized for SWIP
getValue(Num, [Num,Num]) :-
	rational(Num).          % rationals (rarest case) 

% set current value (assumes bounds check has already been done)
putValue_(Val, Int, Nodelist) :-      % update bounds and return node list
	get_attr(Int, clpBNR, Def),       %%SWIP
	setarg(2,Def,Val),                % write new value, undone on backtracking
	arg(3,Def,Nodelist).              %% Def = interval(_Type, _Prev, Nodelist)

%
% Test for interval:
%
%
%  interval(X)  - filter
%
interval(X) :- interval_object(X,_,_,_).

%
% SWIP hooks (ignores the constraint network, i.e., node lists)
%
attribute_goals(X) -->
	{
	 interval_object(X, Type, Val, _Nodelist),
	 interval_domain_(Type, Val, Dom)
	},
	[X::Dom].

attr_portray_hook(interval(T,Val,NL),_Int) :-
	interval_domain_(T,Val,Dom),
	write(Dom).

interval_domain_(integer,[0,1],boolean) :- !.  % integer(0,1) is synonomous with boolean
interval_domain_(T,[L,H],Dom) :-
	interval_bound_(L,LB),
	interval_bound_(H,HB),
	Dom=..[T,LB,HB].

interval_bound_(B,B)   :- number(B),!.
interval_bound_(R,M/N) :- rational(R,M,N). % SWIP - may change if rational fraction ever becomes a number

%
%  range(Int, Bounds) for compatability 
%
% for interval(Int) and numeric(Int), check if value is (always) in specified range, unifying any vars with current value
range(Int, [L,H]) :- getValue(Int, [IL,IH]), !,  % existing interval
	(var(L) -> L=IL ; L=<IL),  % range check, no narrowing
	(var(H) -> H=IH ; IH=<H).
% for var(Int), constrain it to be an interval with specified bounds (like a declaration)
range(Int, [L,H]) :- var(Int),  % new interval
	int_decl_(real, [L,H], Int),
	getValue(Int, [L,H]).       % will bind any intput var's to values

%
%  domain(Int, Dom) for interval(Int) for compatability 
%
domain(Int, Dom) :- 
	interval_object(Int, Type, Val, _),
	interval_domain_(Type, Val, Dom).

%
% Interval declarations
%
Ints::Dom :- is_list(Ints),!,
	intervals_(Ints,Dom).
	
R::Dom :- var(R), var(Dom), !,  % declare R = real(L,H), Note: R can be interval 
	int_decl_(real,[L,H],R),
	domain(R,Dom).

R::Dom :-  var(Dom), !,         % domain query (if interval(R) else fail)
	domain(R,Dom). % "domain" query, unify interval Type and Bounds

R::Dom :-                       % interval(R) or numeric(R) and nonvar(Dom) 
	Dom=..[Type|Bounds],
	int_decl_(Type,Bounds,R).

int_decl_(boolean,_,R) :- !,                % boolean is integer; 0=false, 1=true, ignore any bounds.
	int_decl_(integer,[0,1],R).
	
int_decl_(Type,[L,H],R) :- interval_object(R,IType,Current,_NL), !,  % already interval
	lower_bound_val_(Type,L,IL),  % changing type,bounds?
	upper_bound_val_(Type,H,IH),
	applyType_(Type, IType, R, T/T, Agenda),              % coerce reals to integers (or no-op).
	^(Current,[IL,IH],New),       % low level functional primitive
	updateValue_(Current, New, R, 1, Agenda, NewAgenda),  % update value
	stable_(NewAgenda).           % then execute Agenda

int_decl_(Type,[L,H],R) :- var(R), !,        % new interval (R can't be existing interval)
	lower_bound_val_(Type,L,IL),
	upper_bound_val_(Type,H,IH),
	IL=<IH,           % valid range
	(IL=IH -> R=IL ;  % point range, can unify now
		(put_attr(R, clpBNR, interval(Type, [IL,IH], _NL)),  % attach clpBNR attribute
		 constrainInteger_(Type,R,_)         % creation, so no need to stabilize constraint network
		)
	).

int_decl_(Type,[L,H],R) :- (Type=integer -> integer(R) ; numeric(R)), !,    % R already a point value, check range
	lower_bound_val_(Type,L,IL), IL=<R,
	upper_bound_val_(Type,H,IH), R=<IH.

int_decl_(Type,[],R) :- !,                   % no bounds, fill with vars
	int_decl_(Type,[L,H],R).

intervals_([],_Def).
intervals_([Int|Ints],Def) :-
	Int::Def, !,
	intervals_(Ints,Def).

lower_bound_val_(Type,L,IL) :- var(L), !,  % unspecified bound, make it finite
	finite_interval(Type,[IL,IH]).
lower_bound_val_(real,M/N,IL) :- integer(M), integer(N), !,   % fraction, convert to rational
	IL is M rdiv N.
lower_bound_val_(real,L,IL) :-             % real: evaluate and round outward (if float)
	IL isL L.
lower_bound_val_(integer,L,IL) :-          % integer: evaluate, fail if infinite else make integer
	catch(V is L,_,fail),                  % any evaluation error is failure
	%abs(V)=\=1.0Inf, IL is ceiling(V).
	(abs(V) =:= inf -> IL=V ; IL is ceiling(V)).  % SWIP calculation of ceiling(inf) incorrect

upper_bound_val_(Type,H,IH) :- var(H), !,  % unspecified bound, make it finite
	finite_interval(Type,[IL,IH]).
upper_bound_val_(real,M/N,IH) :- integer(M), integer(N), !,   % fraction, convert to rational
	IH is M rdiv N, !.
upper_bound_val_(real,H,IH) :-             % real: evaluate and round outward (if float)
	IH isH H.
upper_bound_val_(integer,H,IH) :-          % integer: evaluate, fail if infinite else make integer
	catch(V is H,_,fail),                  % any evaluation error is failure
	%abs(V)=\=1.0Inf, IH is floor(V).
	(abs(V) =:= inf -> IH=V ; IH is floor(V)).  % SWIP calculation of floor(inf) incorrect

applyType_(boolean, real, Int, Agenda, NewAgenda) :- !,     % narrow real to boolean
	applyType_(integer, real, Int, Agenda, NewAgenda).
applyType_(integer, real, Int, Agenda, NewAgenda) :- !,     % narrow real to integer
	get_attr(Int, clpBNR, Def),   %% SWIP
	setarg(1,Def,integer),               % set Type (only case allowed)
	constrainInteger_(integer, Int, Nodes),  % add integral constraint
	linkNodeList_(Nodes, Agenda, NewAgenda).
applyType_(Type,IType,Int, Agenda, Agenda).                       % anything else: no change

constrainInteger_(integer,R,[Node]) :- !, Node=node(integral,P,L,R), addNode_([R],Node).
constrainInteger_(_,_,[]).

%
% this goal gets triggered whenever an interval is unified, valid for a numeric value or another interval
%
attr_unify_hook(interval(Type,[L,H],Nodelist), V) :-     % unify an interval with a numeric
	(Type=integer -> integer(V) ; numeric(V)), !,        % check that V is consistent with Type
	L=<V, V=<H,              % in range
	linkNodeList_(Nodelist, T/T, Agenda),
	stable_(Agenda).         % broadcast change

attr_unify_hook(interval(Type1,V1,Nodelist1), Int) :-    % unifying two intervals
	get_attr(Int, clpBNR, Def),         %%SWIP Def = interval(Type, Val, Nodelist)
	Def = interval(Type2, V2, Nodelist2),  % fails on Type mismatch,
	mergeType_(Type1, Type2, NewType),  % unified Type=integer if either is an integer
	^(V1,V2,V),                         % unified range is intersection (from ia_primitives),
	mergeNodes_(Nodelist2,Nodelist1,Newlist),  % unified node list is a merge of two lists
	setarg(1,Def,NewType),              % update new type, value and constraint list, undone on backtracking
	setarg(2,Def,V),
	setarg(3,Def,Newlist),
	linkNodeList_(Newlist, T/T, Agenda),
	stable_(Agenda).         % broadcast change

mergeType_(real, real, real) :- !.
mergeType_(_,    _,    integer).

mergeNodes_([N],NodeList,NodeList) :- var(N),!.
mergeNodes_([N|Ns],NodeList,[N|NewList]) :-
	N=..[node,Op,_,_|Ops],
	notIn_(NodeList,Op,Ops), !,  % test for equivalent node already in NodeList
	mergeNodes_(Ns,NodeList,NewList).
mergeNodes_([N|Ns],NodeList,NewList) :-
	mergeNodes_(Ns,NodeList,NewList).

notIn_([N|Ns],Op,Ops) :-  % equivalent node(Op, _, _|Ops) ==> failure 
	nonvar(N),  % avoids exception in =../2
	N=..[node,Op,_,_|NOps],
	NOps==Ops,  % avoid unification of operands
	!, fail.
notIn_([N|Ns],Op,Ops) :-  % keep searching
	nonvar(N), !,
	notIn_(Ns,Op,Ops).
notIn_(_,_,_).            % end of search

%
% New Constraints use { ... } syntax.
%
{}.
{Cons} :-
	addConstraints_(Cons,T/T,Agenda),         % add constraints
%	traceNew_(Cons),
	stable_(Agenda).                          % then execute Agenda

addConstraints_((C1,C2),Agenda,NewAgenda) :-  % Note: comma as operator
	!,
	constraint_(C1),   % a constraint is a boolean expression that evaluates to true
	simplify(C1,CS1),  % optional
	build_(CS1, 1, boolean, Agenda, NextAgenda),
	addConstraints_(C2,NextAgenda,NewAgenda).
addConstraints_(C,Agenda,NewAgenda) :-
	constraint_(C),    % a constraint is a boolean expression that evaluates to true
	simplify(C,CS),    % optional
	build_(CS, 1, boolean, Agenda, NewAgenda).

:- include(ia_simplify).  % simplifies constraints to a hopefully more efficient equivalent

%
% build a node from an expression
%
build_(Int, Int, VarType, Agenda, NewAgenda) :-     % existing interval object
	interval_object(Int, Type, _, _), !,
	applyType_(VarType, Type, Int, Agenda, NewAgenda).   % coerces exsiting intervals to required type
build_(Var, Var, VarType, Agenda, Agenda) :-        % implicit interval creation.
	var(Var), !,
	universal_interval(U),
	int_decl_(VarType,U,Var).
build_(Num, Int, _, Agenda, Agenda) :-              % floating point constant, may not be precise
	float(Num), !,
	Int::real(Num,Num).                             % will be fuzzed, so not a point
build_(Num, Num, _, Agenda, Agenda) :-              % rational numeric value is precise
	rational(Num), !.  %%integer(Num), !.
	% rational(Num,M,N), C is M/N, !.  %%integer(Num), !.
build_(pt(Num), Num, _, Agenda, Agenda) :-          % point value, must be a number
	numeric(Num), !.
build_(Exp, Int, VarType, Agenda, NewAgenda) :-
	ground(Exp),                                    % ground exp which evaluates to a number
	catch(V is Exp, _, fail),                       % also catches symbolic "numbers", e.g., inf, pi, ..
	build_(V, Int, VarType, Agenda, NewAgenda), !.  % may be fuzzed, so not a point
build_(Exp, Z, _, Agenda, NewAgenda) :-
	Exp =.. [F|Args],
	fmap_(F,Op,[Z|Args],ArgsR,Types), !,
	build_args_(ArgsR,Objs,Types,Agenda,ObjAgenda),
	newNode_(Op,Objs,ObjAgenda,NewAgenda).

build_args_([],[],_,Agenda,Agenda).
build_args_([Arg|ArgsR],[Obj|Objs],[Type|Types],Agenda,NewAgenda) :-
	build_(Arg,Obj,Type,Agenda,NxtAgenda),
	build_args_(ArgsR,Objs,Types,NxtAgenda,NewAgenda).

constraint_(C) :- nonvar(C), C =..[Op|_], fmap_(Op,_,_,_,[boolean|_]), !.  %  a constraint must evaluate to a boolean

fmap_(+,    add,   ZXY,     ZXY,     [real,real,real]).
fmap_(-,    add,   [Z,X,Y], [X,Z,Y], [real,real,real]).     % note subtract before minus 
fmap_(*,    mul,   ZXY,     ZXY,     [real,real,real]).
fmap_(/,    mul,   [Z,X,Y], [X,Z,Y], [real,real,real]).
fmap_(**,   pow,   ZXY,     ZXY,     [real,real,real]).
fmap_(min,  min,   ZXY,     ZXY,     [real,real,real]).
fmap_(max,  max,   ZXY,     ZXY,     [real,real,real]).
fmap_(==,   eq,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(is,   eq,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(<>,   ne,    ZXY,     ZXY,     [boolean,integer,integer]).
fmap_(=<,   le,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>=,   le,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<,    lt,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>,    lt,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<=,   sub,   ZXY,     ZXY,     [boolean,real,real]).  % inclusion/subinterval
fmap_(=>,   sub,   [Z,X,Y], [Z,Y,X], [boolean,real,real]).  % inclusion/subinterval

fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(sqrt,pow,   [Z,X],    [X,Z,2], [real,real,integer]).
fmap_(-,   minus, [Z,X],    [Z,X],   [real,real]).
fmap_(~,   not,   ZX,       ZX,      [boolean,boolean]).
fmap_(exp, exp,   ZX,       ZX,      [real,real]).
fmap_(log, exp,   [Z,X],    [X,Z],   [real,real]).
fmap_(abs, abs,   ZX,       ZX,      [real,real]).
fmap_(sin, sin,   ZX,       ZX,      [real,real]).
fmap_(asin,sin,   [Z,X],    [X,Z],   [real,real]).
fmap_(cos, cos,   ZX,       ZX,      [real,real]).
fmap_(acos,cos,   [Z,X],    [X,Z],   [real,real]).
fmap_(tan, tan,   ZX,       ZX,      [real,real]).
fmap_(atan,tan,   [Z,X],    [X,Z],   [real,real]).

%
% Node constructor
%
newNode_(Op, Args, Agenda, NewAgenda) :-
	NewNode =.. [node, Op, P, L|Args],
	addNode_(Args,NewNode),
	linkNode_(Agenda, NewNode, NewAgenda).

addNode_([],_Node).
addNode_([Arg|Args],Node) :-
	(interval_object(Arg, _Type, _Val, Nodelist) -> newmember(Nodelist, Node) ; true),
	addNode_(Args,Node).

% extend list with X
newmember([X|Xs],N) :- 
	nonvar(X), !,       % not end of (indefinite) list
	newmember(Xs,N).
newmember([N|_],N).     % end of list

%
% Process Agenda to narrow intervals
%
stable_(Agenda) :-
	current_prolog_flag(clpBNR_iteration_limit,Ops),  % budget for current operation
	stableLoop_(Agenda,Ops).

stableLoop_([]/[], OpsLeft) :- !,           % terminate successfully when agenda comes to an end
	nb_getval(clpBNR_iterations_,Cur),      % maintain "low" water mark (can be negative)
	(OpsLeft<Cur -> nb_setval(clpBNR_iterations_,OpsLeft);true).
stableLoop_([Node|Agenda]/T, OpsLeft) :-
	doNode_(Node, OpsLeft, Agenda/T, NewAgenda), !,
	nb_setarg(3,Node,0),                    % reset linked bit
	RemainingOps is OpsLeft-1,              % decrement OpsLeft (can go negative)
	stableLoop_(NewAgenda,RemainingOps).
stableLoop_(Agenda, OpsLeft) :-             % doNode_ failed
	stableLoop_([]/[], OpsLeft),            % discard Agenda
	fail.                                   % and fail

% support for max_iterations statistic
clpStatistics :-
	current_prolog_flag(clpBNR_iteration_limit,L), nb_setval(clpBNR_iterations_,L),  % set "low" water mark to upper limit
	fail.  % backtrack to reset other statistics.

clpStatistic(max_iterations(O/L)) :-
	nb_getval(clpBNR_iterations_,Ops),
	current_prolog_flag(clpBNR_iteration_limit,L),
	O is L-Ops.  % convert "low" water mark to high water mark

%
% Execute a node on the queue
%
doNode_(node(instantiate,P,_,Int,Pt), _, Agenda, Agenda) :-  % frozen constraints must be run as stable_/1 step
	!, Int=Pt.  % cut before 'thaw', constraints run now on thaw
doNode_(Node, OpsLeft, Agenda, NewAgenda) :-
	Node =.. [node,Op,P,L|Args],
	var(P), !,                             % check persistent bit
	marshal_args_(Args,PrimArgs),
	evalNode(Op, P, PrimArgs, New),        % can fail causing stable_ to fail => backtracking
%	traceIntOp_(Op, Args, PrimArgs, New),  % in ia_utilities
	update_values_(PrimArgs, New, Args, OpsLeft, Agenda, NewAgenda),
	(ground(Args) -> P=p;true).            % conditionally set persistent bit
doNode_(Node, OpsLeft, Agenda, Agenda).    % persistent bit "set", skip node

marshal_args_([],[]).
marshal_args_([A|Args],[P|PrimArgs]) :-
	getValue(A,P),
	marshal_args_(Args,PrimArgs).

update_values_([], [], [], _, Agenda, Agenda).
update_values_([P|PrimArgs], [N|New], [A|Args], OpsLeft, Agenda, NewAgenda) :-
	updateValue_(P, N, A, OpsLeft, Agenda, NxtAgenda),
	update_values_(PrimArgs, New, Args, OpsLeft, NxtAgenda, NewAgenda).

%
% Any changes in interval values should come through here.
%
updateValue_(Old, Old, _, _, Agenda, Agenda) :- !.                  % no change in value
updateValue_(_Old, [Pt,Pt], Int, _, Agenda, NewAgenda) :- !,        % Point value ==> update value
	putValue_([Pt,Pt], Int, Nodelist),  % ignore node list, will run via 'instantiate' node
	linkNode_(Agenda,node(instantiate,P,L,Int,Pt), NewAgenda).      % add 'instantiate' node to Agenda
updateValue_(Old, New, Int, OpsLeft, Agenda, NewAgenda) :-          % set value to New
	% NewL=<NewH,  % check unnecessary if primitives do their job
	putValue_(New, Int, Nodelist),                      % update value
	(propagate_if_(OpsLeft, Old, New)                   % if OpsLeft >0 or narrowing sufficent
		-> linkNodeList_(Nodelist, Agenda, NewAgenda)   % then propagate change
		 ; NewAgenda = Agenda                           % else continue with remaining Agenda
	).

propagate_if_(Ops, _, _)           :- Ops>0.  % ! unnecessary since it's used in '->' test
propagate_if_(_, [OH,OL], [NH,NL]) :- catch((NH-NL)/(OH-OL) < 0.9,_,true).  % any overflow in calculation will propagate

linkNodeList_([X|Xs], List, NewList) :-
	nonvar(X),                                     % not end of list ...
	arg(3,X,0),                                    % not linked and ...
	arg(2,X,P), var(P), !,                         % not persistent ->
	linkNode_(List, X, NextList),                  % add to list
	linkNodeList_(Xs, NextList, NewList).
linkNodeList_([X|Xs], List, NewList) :-            % skip node until end of list
	nonvar(X), !,
	linkNodeList_(Xs, List, NewList).
linkNodeList_(_, List, List).                      % end of indefinite node list (don't make it definite)

linkNode_(List/[X|NextTail], X, List/NextTail) :-
	setarg(3,X,1).                                 %% SWIP set linked bit, reset on backtracking

:- include(ia_utilities).  % print,solve, etc.

%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).

% end of reset chain succeeds. Need cut since predicate is "discontiguous".
clpStatistics :- !.

:- initialization((
	nl,write("*** clpBNR v0.7alpha ***"),nl,
	set_prolog_stack(global,min_free(8196)),
	create_prolog_flag(clpBNR_iteration_limit,10000,[type(integer)]),
	create_prolog_flag(clpBNR_default_precision,6,[type(integer)]),
	clpStatistics
)).
