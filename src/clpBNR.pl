%
% CLP(BNR) == Constraints On Boolean, Integer, and Real Intervals
%
:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfy, ::),
	(::)/2,                % declare interval
	{}/1,                  % add constraint
	interval/1,            % filter for clpBNR constrained var
	list/1,                % for compatability
	range/2,               % for compatability
	lower_bound/1,         % narrow interval to point equal to lower bound
	upper_bound/1,         % narrow interval to point equal to upper bound

	% constraint operators
	op(200, fy, ~),        % boolean 'not'
	op(500, yfx, and),     % boolean 'and'
	op(500, yfx, or),      % boolean 'or'
	op(500, yfx, nand),    % boolean 'nand'
	op(500, yfx, nor),     % boolean 'nor'
	op(500, yfx, xor),     % boolean 'xor'
	op(700, xfx, <>),      % integer
	op(700, xfx, <=),      % set inclusion
	op(700, xfx, =>),      % set inclusion

	% utilities
	print_interval/1,      % print interval as list of two numbers (for compatability)
	solve/1, solve/2,      % solve (list of) intervals using split
	enumerate/1,           % "enumerate" integers
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1        % get all defined in a list
	]).

	
/* missing(?) functionality:

1. arithmetic functions on intervals (delta, median, midpoint). Requires hooking is/2.
	
2. utilities accumulate/2 and absolve/1.

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
%  list/1 filter
%
list(L) :- is_list(L).     %%SWIP

:- include(ia_primitives).  % interval arithmetic relations via evalNode/4.

%
% Intervals are constrained (frozen) variables.
%
% Current interval bounds updates via setarg(Val) which is backtrackable
%

interval_object(Int, Type, Val, Nodelist) :-
	% frozen(Int, clpBNR:intdef_(Int, Type, Val, Nodelist)).
	get_attr(Int, freeze, clpBNR:intdef_(Int, Type, Val, Nodelist)).       %%SWIP

% get current value
getValue(Num, Val) :-
	number(Num), !,
	Val=[Num,Num].                    % numeric value
getValue(Int, Val) :-                 % assumed to be an interval
	%	frozen(Int, clpBNR:intdef_(Int, _Type, Val, _Nodelist)), !.
	get_attr(Int, freeze, clpBNR:intdef_(Int, _Type, Val, _Nodelist)).     %%SWIP
	
% set current value
putValue_(Val, Int, Nodelist) :-      % update bounds and return node list
	Val=[L,H], L=<H,
	%	frozen(Int, clpBNR:Def),
	get_attr(Int, freeze, clpBNR:Def),                                     %%SWIP
	Def = intdef_(Int, _Type, _Prev, Nodelist),
	setarg(3,Def,Val).                % undone on backtracking

%
% Test for interval:
%
%
%  interval(X)  - filter
%
interval(X) :- interval_object(X,_,_,_).


%
% Interval declarations
%
:- op(700, xfy, ::).

Ints::Type :- list(Ints),!,
	intervals_(Ints,Type).
	
R::real :-
	interval_object(R,_Type,[L,H],_NL), !,  % already interval, use current value
	makeInterval_(R, real, [L,H]).
R::real :- !,
	R::real(_L,_H).
R::real(L,H) :- !,
	fuzz_(lo,L,LL), fuzz_(hi,H,HH),         % floating point constants need to be fuzzed
	fillDefaults_(real,[LL,HH]),
	makeInterval_(R, real, [LL,HH]).
	
I::integer :-
	interval_object(I,_Type,[L,H],_NL), !,  % already interval, use current value
	makeInterval_(I, integer, [L,H]).
I::integer :- !,
	I::integer(_L,_H).
I::integer(L,H) :- !,
	fillDefaults_(integer,[L,H]),
	integer([L,H],[IL,IH]),                 % will inward round any floats
	makeInterval_(I, integer, [IL,IH]).
	
B::boolean :-                               % set to integer(0,1)
	B::integer(0,1).

intervals_([],_Type).
intervals_([Int|Ints],Type) :-
	Int::Type, !,
	intervals_(Ints,Type).

fillDefaults_(Type,[L,H]) :-
%	universal_interval([FL,FH]),    % more useful to default to finite intervals, very weak narrowing on infinities
	finite_interval(Type,[FL,FH]),
	(L=FL;true),
	(H=FH;true),!.

fuzz_(_,B,FB)  :- number(B), 0 =:= float_fractional_part(B), !, FB is float(B).  % integral values assumed precise
fuzz_(lo,L,LL) :- float(L),!, LL isL L.           % fuzz floats with fractional components
fuzz_(hi,H,HH) :- float(H),!, HH isH H.
%fuzz_(_,B,FB)  :- integer(B),!, FB is float(B).  % integers assumed precise, (floating big integers?)
fuzz_(_,B,B).                                     % vars will get default values

makeInterval_(Int, Type, [L,H]) :-
	interval_object(Int, IType, _, _), !,  % already an interval object
	applyType_(Type, IType, Int),          % coerce reals to integers (or no-op).
	setInterval_(Int, L, H).               % set bounds (may fail if no intersection with current value)
	
makeInterval_(Int, Type, Val) :-
	var(Int), !,                 % an (unconstrained) variable
	freeze(Int, intdef_(Int, Type, Val, _NL)),       % freeze interval
	(Type=integer -> addOp_(node(integral,P,L,Int,0),Int) ; true).  %% if integer add custom node - not externally available

makeInterval_(Int, _Type, [L,H]) :- L=<Int, Int=<H.  % just a range test on a number
	
% this goal gets triggered whenever an interval is unified with a hopefully numeric value
intdef_(Int, Type, [L,H], Nodelist) :-
	number(Int),                % must be a number
	L=<Int, Int=<H,             % check in case not generated from evalNode_
	linkNodeList_(Nodelist, T/T, Agenda),
	stable_(Agenda).        % broadcast change, note variable now instantiated so no need to change Value

applyType_(integer, real, Int) :- !,     % narrow real to integer
	get_attr(Int, freeze, clpBNR:Def),   %% SWIP
	setarg(2,Def,integer),               % set Type (only case allowed)
	addOp_(node(integral,P,Int,0),Int).  % add integral constraint
applyType_(Type,IType,Int).                       % anything else: no change

setInterval_(Int, L, H) :-      % new interval value, used by makeInterval_ and range/2,3
	getValue(Int,Current),      % current and new values must intersect
	^(Current,[L,H],New),       % low level functional primitive
	updateValue_(Current, New, Int, T/T, NewAgenda),
	stable_(NewAgenda).

%
%  lower_bound and upper_bound
%
lower_bound(Int) :- 
	getValue(Int,[L,H]),
	updateValue_([L,H], [L,L], Int, T/T, NewAgenda),
	stable_(NewAgenda).

upper_bound(Int) :-
	getValue(Int,[L,H]),
	updateValue_([L,H], [H,H], Int, T/T, NewAgenda),
	stable_(NewAgenda).

%
%  range(Int, Bounds) for compatability - defaults to range(Int, real, Bounds)
%
range(Int, Bounds) :-
	range(Int, real, Bounds).

%
%  range(Int, Type, Bounds) - currently not available outside module
%
range(Int, Type, Bounds) :-     % get current counds
	interval(Int),
	getValue(Int, Bounds) , !.  % fails if Value \= Bounds.
	
range(Int, Type, [L,H]) :-      % set new bounds on existing interval
	interval(Int),
	setInterval_(Int, L, H), !. %% Int::Type(L,H)

range(Int, Type, Bounds) :-     % create new interval
	var(Int), !,
	Spec =.. [Type|Bounds],
	Int::Spec.


%
% New Constraints use { ... } syntax.
%
{}.
{Cons} :-
	addConstraints_(Cons,T/T,Agenda),  % add constraints then
	stable_(Agenda).                   % execute Agenda

addConstraints_((C1,C2),Agenda,NewAgenda) :-
	!,
	build_(C1, 1, boolean, Agenda, NextAgenda),   % a constraint is a expression that must evaluate to true
	addConstraints_(C2,NextAgenda,NewAgenda).
addConstraints_(C,Agenda,NewAgenda) :-
	build_(C, 1, boolean, Agenda, NewAgenda).     % a constraint is a expression that must evaluate to true

%
% build a node from an expression
%
build_(Int, Int, VarType, _) :-                   % existing interval object
	interval_object(Int, Type, _, _), !,
	applyType_(VarType, Type, Int).               % coerces exsiting intervals to required type
build_(Var, Var, VarType, Agenda, Agenda) :-                 % implicit interval creation.
	var(Var), !,
	Var::VarType.
build_(Num, Int, _, Agenda, Agenda) :-                       % floating point constant, may not be precise
	float(Num), !,
	Int::real(Num,Num).                           % will be fuzzed, so not a point
build_(Num, Num, _, Agenda, Agenda) :-                       % integer numeric value is precise
	integer(Num), !.
build_(pt(Num), Num, _, Agenda, Agenda) :-                   % point value
	number(Num), !.
build_(Exp, Int, VarType, Agenda, NewAgenda) :-
	ground(Exp),                                  % ground exp which evaluates to a number
	catch(V is Exp, _, fail),                     % also catches symbolic "numbers", e.g., inf, pi, ..
	build_(V, Int, VarType, Agenda, NewAgenda), !.           % may be fuzzed, so not a point
build_(Exp*X, Z, _, Agenda, NewAgenda):-                     % map X*X*X... to X**N
	mulPower_(Exp,X,1,NExp),!,
	build_(NExp, Z, _, Agenda, NewAgenda).
build_(sqrt(X), Z, _, Agenda, NewAgenda) :-                  % map Z=sqrt(X) to X=Z**2 
	!,
	build_(Z**2, X, _, Agenda, NewAgenda).

build_(Exp, Z, _, Agenda, NewAgenda) :-   % Exp = X+Y, X*Y, min(X,Y), etc.
	Exp =.. [F,X,Y],                                % create ternary node
	fmap_(F, Op, [Z,X,Y], [Zarg,Xarg,Yarg], [Ztype,Xtype,Ytype]),!,
	build_(Xarg, Xobj, Xtype, Agenda, XAgenda),
	build_(Yarg, Yobj, Ytype, XAgenda, XYAgenda),
	build_(Zarg, Zobj, Ztype, XYAgenda, XYZAgenda),
	newNode_(Op, Zobj, Xobj, Yobj, XYZAgenda, NewAgenda).

build_(Exp, Z, _, Agenda, NewAgenda) :-   % Exp = -X, exp(X), sin(x) etc.
	Exp =.. [F,X],                                  % create binary node
	fmap_(F, Op, [Z,X,_], [Zarg,Xarg,_], [Ztype,Xtype,xx]), !, % use Ytype to disambiguate, e.g., subtract and minus
	build_(Xarg, Xobj, Xtype, Agenda, XAgenda),
	build_(Zarg, Zobj, Ztype, XAgenda, XZAgenda),
	newNode_(Op, Zobj, Xobj, XZAgenda, NewAgenda).

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
fmap_(<,    lt,    ZXY,     ZXY,     [boolean,integer,integer]).
fmap_(>,    lt,    [Z,X,Y], [Z,Y,X], [boolean,integer,integer]).
fmap_(<=,   sub,   ZXY,     ZXY,     [boolean,real,real]).  % inclusion/subinterval
fmap_(=>,   sub,   [Z,X,Y], [Z,Y,X], [boolean,real,real]).  % inclusion/subinterval

fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(-,   minus, ZX,       ZX,      [real,real,xx]).
fmap_(~,   not,   ZX,       ZX,      [boolean,boolean,xx]).
fmap_(exp, exp,   ZX,       ZX,      [real,real,xx]).
fmap_(log, exp,   [Z,X,Y],  [X,Z,Y], [real,real,xx]).
fmap_(abs, abs,   ZX,       ZX,      [real,real,xx]).
fmap_(sin, sin,   ZX,       ZX,      [real,real,xx]).
fmap_(asin,sin,   [Z,X,Y],  [X,Z,Y], [real,real,xx]).
fmap_(cos, cos,   ZX,       ZX,      [real,real,xx]).
fmap_(acos,cos,   [Z,X,Y],  [X,Z,Y], [real,real,xx]).
fmap_(tan, tan,   ZX,       ZX,      [real,real,xx]).
fmap_(atan,tan,   [Z,X,Y],  [X,Z,Y], [real,real,xx]).

% used to map X*X*X... to X**N
mulPower_(Exp*X1,X,C,NExp):-
	X1 == X, !,
	C1 is C+1,
	mulPower_(Exp,X,C1,NExp).
mulPower_(Exp,X,C,X**N) :- 
	X==Exp, !, 
	N is C+1.  % test and count X*X*X*...
mulPower_(Exp,X,N,Exp*X**N) :-
	N>1.  % fails to standard 'mul' if only 1 X collected.

%
% Node constructors
%
newNode_(Op, Z, X, Agenda, NewAgenda) :-     % binary
	NewNode = node(Op, P, L, Z, X),  % mark as linked
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	linkNode_(Agenda, NewNode, NewAgenda).

newNode_(Op, Z, X, Y, Agenda, NewAgenda) :-  % ternary
	NewNode = node(Op, P, L, Z, X, Y),  % mark as linked
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	addOp_(NewNode, Y),
	linkNode_(Agenda, NewNode, NewAgenda).

addOp_(Node, Int) :-
	interval_object(Int, _Type, _Val, Nodelist), !, 
	newmember(Nodelist, Node).
addOp_(_Node, _Num).  %% already a number, i.e., no constraints

% extend list with X

newmember([X|Xs],N) :- 
	nonvar(X), !,       % not end of (indefinite) list
	newmember(Xs,N).
newmember([N|_],N).     % end of list

%
% Process Agenda to narrow intervals
%
stable_([]/[]) :- !.                  % terminate when agenda comes to an end

stable_([Node|Agenda]/T) :-
	doNode_(Node, Agenda/T, NewAgenda),
	setarg(3,Node,0),                 % reset linked bit
	stable_(NewAgenda).

doNode_(node(instantiate,P,L,Int,Pt), Agenda, Agenda) :-  % frozen constraints must be run as stable_ step
	var(P), !,
	Int=Pt.                           % constraints run now on thaw
	
doNode_(node(Op,P,L,Z,X,Y), Agenda, NewAgenda) :-  % ternary relation
	var(P), !,                        % check persistent bit
	getValue(Z, ZV),
	getValue(X, XV),
	getValue(Y, YV),
	evalNode(Op, P, [ZV, XV, YV], [NewZ, NewX, NewY]),
%	traceIntOp_(Op, [Z, X, Y], [ZV, XV, YV], [NewZ, NewX, NewY]),  % in ia_utilities
	updateValue_(ZV, NewZ, Z, Agenda, ZAgenda),
	updateValue_(XV, NewX, X, ZAgenda, ZXAgenda),
	updateValue_(YV, NewY, Y, ZXAgenda, NewAgenda),
	(ground([Z,X,Y]) -> P=p ; true).  % conditionally set persistent bit
	
doNode_(node(Op,P,L,Z,X), Agenda, NewAgenda) :-    % binary relation
	var(P), !,                        % check persistent bit
	getValue(Z, ZV),
	getValue(X, XV),
	evalNode(Op, P, [ZV, XV], [NewZ, NewX]),
%	traceIntOp_(Op, [Z, X], [ZV, XV], [NewZ, NewX]),  % in ia_utilities
	updateValue_(ZV, NewZ, Z, Agenda, ZAgenda),
	updateValue_(XV, NewX, X, ZAgenda, NewAgenda),
	(ground([Z,X]) -> P=p ; true).   % conditionally set persistent bit
	
doNode_(Node, Agenda, Agenda).          % persistent bit "set", skip node

%
% Any changes in interval values should come through here.
%
updateValue_(Old, Old, _, Agenda, Agenda) :- !.                 % no change in value
updateValue_(_Old, [Pt,Pt], Int, Agenda, NewAgenda) :- !,       % Point value ==> update value
	putValue_([Pt,Pt], Int, Nodelist),             % ignore node list, will run via 'instantiate' node
	linkNode_(Agenda,node(instantiate,P,L,Int,Pt), NewAgenda).  % add 'instantiate' node to Agenda
updateValue_(_Old, New, Int, Agenda, NewAgenda) :-              % set value to New
	putValue_(New, Int, Nodelist),                 % update value
	linkNodeList_(Nodelist, Agenda, NewAgenda).    % add constraints to agenda for execution


linkNodeList_(Xs, List, List) :- var(Xs), !.       % end of indefinite node list
linkNodeList_([X|Xs], List, NewList) :-
	arg(3,X,0),                                    % not linked and ...
	arg(2,X,P), var(P), !,                         % not persistent ->
	linkNode_(List, X, NextList),                  % add to list
	linkNodeList_(Xs, NextList, NewList).
linkNodeList_([X|Xs], List, NewList) :-            % skip node
	linkNodeList_(Xs, List, NewList).

linkNode_(List/[X|NextTail], X, List/NextTail) :-
	setarg(3,X,1).                                 %% SWIP set linked bit


:- include(ia_utilities).  % print,solve, etc

%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).

% end of reset chain succeeds. Need cut since predicate is "discontiguous".
clpStatistics :- !.

:- initialization((
	nl,write("*** clpBNR v0.6alpha ***"),nl,
	set_prolog_stack(global,min_free(1024)),
	clpStatistics
)).
