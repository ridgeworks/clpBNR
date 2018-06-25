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

:- initialization(
	set_prolog_flag(singleton_warning,off)
	).
				
%
%  list/1 filter
%
list(L) :- is_list(L).     %%SWIP


:- discontiguous(clpStatistics/0, clpStatistic/1).

:- include(ia_primitives).

%
% Intervals are constrained (frozen) variables.
%
% Current interval bounds updates via setarg(Val) which is backtrackable
%

interval_object(Int, Type, Val, Nodelist) :-
	frozen(Int, clpBNR:intdef_(Int, Type, Val, Nodelist)).

% get current value
getValue(Num, Val) :-
	number(Num), !,
	Val=[Num,Num].                    % numeric value
getValue(Int, Val) :-                 % assumed to be an interval
	%	frozen(Int, clpBNR:intdef_(Int, _Type, Val, _Nodelist)), !.
	get_attr(Int, freeze, clpBNR:intdef_(Int, _Type, Val, _Nodelist)), !.     %%SWIP
	
% set current value
putValue_(Val, Int, Nodelist) :-      % update bounds and return node list
	Val=[L,H], L=<H,
	%	frozen(Int, clpBNR:Def),
	get_attr(Int, freeze, clpBNR:Def),     %%SWIP
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
	
R::real :- !,
	R::real(_L,_H).
R::real(L,H) :- !,
	fuzz_(lo,L,LL), fuzz_(hi,H,HH),  % floating point constants need to be fuzzed
	fillDefaults_(real,[LL,HH]),
	makeInterval_(R, real, [LL,HH]).
	
I::integer :- !,
	I::integer(_L,_H).
I::integer(L,H) :- !,
	fillDefaults_(integer,[L,H]),
	integer([L,H],[IL,IH]),  % will inward round any floats
	makeInterval_(I, integer, [IL,IH]).
	
B::boolean :-                       % set to [0,1]
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
fuzz_(lo,L,LL) :- float(L),!, LL isL L.          % fuzz floats with fractional components
fuzz_(hi,H,HH) :- float(H),!, HH isH H.
%fuzz_(_,B,FB)  :- integer(B),!, FB is float(B).  % integers assumed precise, (floating big integers?)
fuzz_(_,B,B).                                    % vars will get default values

makeInterval_(Int, _Type, [L,H]) :-
	interval_object(Int, _, _, _), !,  % already an interval object
	setInterval_(Int, L, H).           % just set bounds (may fail if no intersection with current value)
	
makeInterval_(Int, Type, Val) :-
	var(Int), !,                 % an (unconstrained) variable
	freeze(Int, intdef_(Int, Type, Val, _NL)),       % freeze interval
	(Type=integer -> addOp_(node(integral,P,Int,0),Int) ; true).  %% if integer add custom node - not externally available

makeInterval_(Int, _Type, [L,H]) :- L=<Int, Int=<H.  % just a range test on a number
	
% this goal gets triggered whenever an interval is unified with a hopefully numeric value
intdef_(Int, Type, [L,H], Nodelist) :-
	number(Int),                % must be a number
	L=<Int, Int=<H,             % check in case not generated from evalNode_
	stable_(Nodelist).          % broadcast change, note variable now instantiated so no need to change Value
	

setInterval_(Int, L, H) :-      % new interval value, used by makeInterval_ and range/2,3
	getValue(Int,Current),      % current and new values must intersect
	^(Current,[L,H],New),       % low level functional primitive
	updateValue_(Current, New, Int, Agenda),
	stable_(Agenda).

%
%  lower_bound and upper_bound
%
lower_bound(Int) :- 
	getValue(Int,[L,H]),
	updateValue_([L,H], [L,L], Int, Agenda),
	stable_(Agenda).

upper_bound(Int) :-
	getValue(Int,[L,H]),
	updateValue_([L,H], [H,H], Int, Agenda),
	stable_(Agenda).

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
	addConstraints_(Cons,Agenda),  % add constraints then
	stable_(Agenda).               % execute Agenda

addConstraints_((C1,C2),Agenda) :-
	!,
	build_(C1, 1, boolean, Agenda),  % a constraint is a expression that must evaluate to true
	addConstraints_(C2,Agenda).
addConstraints_(C,Agenda) :-
	build_(C, 1, boolean, Agenda).   % a constraint is a expression that must evaluate to true

%
% build a node from an expression
%
build_(Int, Int, _, _) :-                         % existing interval object
	interval_object(Int, _, _, _), !.
build_(Var, Var, VarType, _) :-                   % implicit interval creation.
	var(Var), !,
	Var::VarType.
build_(Num, Int, _, _) :-                         % floating point constant, may not be precise
	float(Num), !,
	Int::real(Num,Num).                           % will be fuzzed, so not a point
build_(Num, Num, _, _) :-                         % integer numeric value is precise
	integer(Num), !.
build_(pt(Num), Num, _, _) :-                     % point value
	number(Num), !.
build_(Exp, Int, VarType, Agenda) :-
	ground(Exp),                                  % ground exp which evaluates to a number
	catch(V is Exp, _, fail),                     % also catches symbolic "numbers", e.g., inf, pi, ..
	build_(V, Int, VarType, Agenda), !.           % may be fuzzed, so not a point
build_(Exp*X, Z, _, Agenda):-                     % map X*X*X... to X**N
	mulPower_(Exp,X,1,NExp),!,
	build_(NExp, Z, _, Agenda).
build_(sqrt(X), Z, _, Agenda) :-                  % map Z=sqrt(X) to X=Z**2 
	!,
	build_(Z**2, X, _, Agenda).

build_(Exp, Z, _, Agenda) :-   % Exp = X+Y, X*Y, min(X,Y), etc.
	Exp =.. [F,X,Y],                                % create ternary node
	fmap_(F, Op, [Z,X,Y], [Zarg,Xarg,Yarg], [Ztype,Xtype,Ytype]),!,
	build_(Xarg, Xobj, Xtype, Agenda),
	build_(Yarg, Yobj, Ytype, Agenda),
	build_(Zarg, Zobj, Ztype, Agenda),
	newNode_(Op, Zobj, Xobj, Yobj, Agenda).

build_(Exp, Z, _, Agenda) :-   % Exp = -X, exp(X), sin(x) etc.
	Exp =.. [F,X],                                  % create binary node
	fmap_(F, Op, [Z,X,_], [Zarg,Xarg,_], [Ztype,Xtype,xx]), !, % use Ytype to disambiguate, e.g., subtract and minus
	build_(Xarg, Xobj, Xtype, Agenda),
	build_(Zarg, Zobj, Ztype, Agenda),
	newNode_(Op, Zobj, Xobj, Agenda).

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
newNode_(Op, Z, X, Agenda) :-     % binary
	NewNode = node(Op, P, Z, X),
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	newmember(Agenda, NewNode).

newNode_(Op, Z, X, Y, Agenda) :-
	NewNode = node(Op, P, Z, X, Y),  % ternary
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	addOp_(NewNode, Y),
	newmember(Agenda, NewNode).

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
stable_([]) :- !.                                     % terminate when agenda comes to an end

stable_([node(instantiate,_P,Int,Pt)|Agenda]) :- !,   % frozen constraints can't be run inside stable_ step
	Int=Pt,                                           % constraints run now on thaw
	stable_(Agenda).                                  % continue with Agenda
	
stable_([node(Op,P,Z,X,Y)|Agenda]) :-                 % ternary relation
	var(P), !,                         % check persistent bit
	getValue(Z, ZV),
	getValue(X, XV),
	getValue(Y, YV),
	evalNode(Op, P, [ZV, XV, YV], [NewZ, NewX, NewY]),
%	traceIntOp_(Op, [Z, X, Y], [ZV, XV, YV], [NewZ, NewX, NewY]),  % in ia_utilities
	CurAgenda = [node(Op,P,Z,X,Y)|Agenda],            % note: Node still on current Agenda
	updateValue_(ZV, NewZ, Z, CurAgenda),
	updateValue_(XV, NewX, X, CurAgenda),
	updateValue_(YV, NewY, Y, CurAgenda),
	nextNode_([Z,X,Y], P, Agenda).     % conditionally set persistent bit and continue with Agenda
	
stable_([node(Op,P,Z,X)|Agenda]) :-                   % binary relation
	var(P), !,                         % check persistent bit
	getValue(Z, ZV),
	getValue(X, XV),
	evalNode(Op, P, [ZV, XV], [NewZ, NewX]),
%	traceIntOp_(Op, [Z, X], [ZV, XV], [NewZ, NewX]),  % in ia_utilities
	CurAgenda = [node(Op,P,Z,X)|Agenda],              % note: Node still on current Agenda
	updateValue_(ZV, NewZ, Z, CurAgenda),
	updateValue_(XV, NewX, X, CurAgenda),
	nextNode_([Z,X], P, Agenda).       % conditionally set persistent bit and continue with Agenda
	
stable_([Node|Agenda]) :-              % persistent bit "set", skip node
	stable_(Agenda).

nextNode_(Args,p,Agenda) :- ground(Args), !, stable_(Agenda).  % args are grounded, set persistent bit
nextNode_(Args,_,Agenda) :- stable_(Agenda).                   % just continue with Agenda

%
% Any changes in interval values should come through here.
updateValue_(Old, Old, _, _) :- !.                 % no change in value
updateValue_(_Old, [Pt,Pt], Int, Agenda) :- !,     % Point value ==> update value and add 'instantiate' node to Agenda
	putValue_([Pt,Pt], Int, _NL),                  % ignore constraints, will run via 'instantiate' node
	ismember(Agenda,node(instantiate,P,Int,Pt)).
updateValue_(_Old, New, Int, Agenda) :-            % set value to New
	putValue_(New, Int, NL),                       % update value
	subset_(NL, Agenda).                           % add constraints to agenda for execution

subset_(Xs, _) :- var(Xs),!.                       % end of indefinite input list
subset_([X|Xs], List) :-
	arg(2,X,P), var(P),                            % X = node(Op, P, _..), not persistent
	ismember(List, X), !,                          % checks for duplicates
	subset_(Xs, List).
subset_([X|Xs], List) :-                           % X is persistent, don't add'
	subset_(Xs, List).

ismember([X|Xs], N) :-
	nonvar(X), !,                                  % test for end of indefinite list
	(N==X                                          % test for duplicate, careful not to unify any operands
		-> true                                    % it's a duplicate, nothing to do
		;  ismember(Xs,N)                          % different, keep scanning
	).
ismember([N|_],  N).                               % end of indefinite list, add node and new tail

/*ismember(256,  _, _) :- !.                        % max queue length reached
ismember(L, [X|Xs], N) :-
	nonvar(X), !,                                  % test for end of indefinite list
	(N==X                                          % test for duplicate, careful not to unify any operands
		-> true                                    % it's a duplicate, nothing to do
		;  (L1 is L+1,ismember(L1,Xs,N))           % different, keep scanning
	).
ismember(_, [N|_],  N).                            % end of indefinite list, add node and new tail
*/


:- include(ia_utilities).

%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).

% end of reset chain succeeds. Need cut since predicate is "discontiguous".
clpStatistics :- !.

:- initialization(clpStatistics).
