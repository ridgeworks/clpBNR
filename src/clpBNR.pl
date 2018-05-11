%
% Constraints On Boolean, Integer, and Real Intervals
%
:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfy, ::),
	(::)/2,                % declare interval
	{}/1,                  % add constraint
	interval/1,            % filter for constrained var
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
				   
	% utilities
	print_interval/1,
	solve/1,
	enumerate/1,
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1        % get all defined in a list
	]).

:- initialization(
	set_prolog_flag(singleton_warning,off)
	).
				
:- discontiguous(clpStatistics/0, clpStatistic/1).

:- include(ia_primitives).

%
% Intervals are constrained (frozen) variables. Ineterval values are stored in globals
%  keyed by atoms of the form @N where N is a positive integer starting at 1.
%
% Test for interval:
%
%
%  interval(X)  - filter
%
interval(X) :- interval_object(X,_,_,_).

interval_object(Int, Type, Id, Nodelist) :-
	frozen(Int, clpBNR:intdef_(Int, Type, Id, Nodelist)).

%
% Interval declarations
%
:- op(700, xfy, ::).

intervals_([],_Type).
intervals_([Int|Ints],Type) :-
	Int::Type, !,
	intervals_(Ints,Type).

Ints::Type :- list(Ints),!,
	intervals_(Ints,Type).
	
R::real :- !,
	R::real(_L,_H).
R::real(L,H) :- !,
	fillDefaults_(real,[L,H]),
	FL is float(L), FH is float(H),
	makeInterval_(R, real, [FL,FH]).
	
I::integer :- !,
	I::integer(_L,_H).
I::integer(L,H) :- !,
	fillDefaults_(integer,[L,H]),
	integer([L,H],[IL,IH]),
	makeInterval_(I, integer, [IL,IH]).  
	
B::boolean :-                         % set to [0,1]
	B::integer(0,1).
	
fillDefaults_(Type,[L,H]) :-
%	universal_interval([FL,FH]),  % more useful to default to finite intervals, very weak narrowing on infinities
	finite_interval(Type,[FL,FH]),
	(L=FL;true),
	(H=FH;true),!.

	
:- initialization(g_zero(makeInterval_)).  % initialize interval ID generator

makeInterval_(Int, _Type, [L,H]) :-
	interval_object(Int, _, Id, _), !, % already an interval object
	setInterval_(Int, L, H).           % just set bounds (may fail if no intersection with current value)
	
makeInterval_(Int, Type, Val) :-
	var(Int), !,                 % an (unconstrained) variable
	BindGoal = intdef_(Int, Type, Id, _NL),
	b_getval(makeInterval_,UNm), % new interval, get last used ID number
	succ(UNm,NNm),               % new ID number
	b_setval(makeInterval_,NNm), % make it used, needs to be undone on backtracking
	number_codes(NNm,S),atom_codes(Id,[64|S]),  % build @N Id
	freeze(Int, BindGoal),       % freeze interval to bind goal
	putValue_(Val, Int, _),      % and put the value, no broadcast required (yet)
	((Type=integer -> addOp_(node(integral,Int,0),Int));true).  %% if integer add custom node - not externally available

makeInterval_(Int, _Type, [L,H]) :- L=<Int, Int=<H.  % just a range test on a number
	
% this goal gets triggered whenever an interval is unified with a hopefully numeric value
intdef_(Int, Type, Id, NL) :-
	number(Int),                % must be a number
	b_getval(Id, [L,H]),        % in interval range
	L=<Int, Int=<H,
	stable_(NL).                % broadcast change, note variable now instantiated so no need to putValue_
	

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
build_(Exp, Exp, VarType, _) :-                   % implicit interval creation.
	var(Exp), !,
%	universal_interval([L,H]),                    % infinte intervals don't narrow, use finite defaults
%	finite_interval(VarType,[L,H]),
%	Spec=..[VarType,L,H],
	Exp::VarType.
build_(Num, Num, _, _) :-                         % numeric value
	number(Num), !.

% this optimization is questionable and needs to be generalized
%build_(Exp, Num, _, _) :-                         % grounded expression, if arithmetic just evaluate
%	ground(Exp),
%	functor(Exp, F, _), fmap_(F, _, _, _, [real,_,_]), !,
%	Num is Exp.
%	nl,print(Exp),fail.  % informal log and fail

build_(Exp*X, Z, _, Agenda):-   % optimixation to convert X*X*X... to X**N
	build_(X, Xarg, real, Agenda),
	mulPower_(Exp,X,1,N),!,
	build_(Z, Zarg, real, Agenda),
	Yarg::integer(N,N),
	newNode_(pip, Zarg, Xarg, Yarg, Agenda).
	
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
fmap_(-,    add,   [Z,X,Y], [X,Z,Y], [real,real,real]).  % note subtract before minus 
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
fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(-,   minus, ZX,       ZX,      [real,real,xx]).
fmap_(exp, exp,   ZX,       ZX,      [real,real,xx]).
fmap_(log, exp,   [Z,X,Y],  [X,Z,Y], [real,real,xx]).
fmap_(abs, abs,   ZX,       ZX,      [real,real,xx]).
fmap_(~,   not,   ZX,       ZX,      [boolean,boolean,xx]).

mulPower_(Exp,X,C,N) :- X==Exp, !, succ(C,N).  % test and count X*X*X*...
mulPower_(Exp*X1,X,C,N):-
	X1 == X,
	succ(C,C1),
	mulPower_(Exp,X,C1,N).

%
% Node constructors
%
newNode_(Op, Z, X, Agenda) :-     % binary
	NewNode = node(Op, Z, X),
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	newmember(Agenda, NewNode).

newNode_(Op, Z, X, Y, Agenda) :-
	NewNode = node(Op, Z, X, Y),  % ternary
	addOp_(NewNode, Z),
	addOp_(NewNode, X),
	addOp_(NewNode, Y),
	newmember(Agenda, NewNode).

addOp_(Node, Int) :-
	interval_object(Int, _Type, _Id, Nodelist), !, 
	newmember(Nodelist, Node).
addOp_(_Node, _Num).  %% already a number, i.e., no constraints

% extend list with X
newmember(Xs,X) :- var(Xs),!,Xs=[X|_].
newmember([_|Xs],X) :- newmember(Xs,X).

%
% Process Agenda to narrow intervals
%
stable_([]) :- !.                      % terminate when agenda comes to an end

stable_([node(instantiate,Int,Pt)|Agenda]) :-  % deferred unification
	!,
	Int=Pt,           % thaws Int and runs any of its constraints
	stable_(Agenda).  % continue with rest of Nodes
		
stable_([node(Op,Z,X,Y)|Agenda]) :-    % ternary relation
	!,
	getValue(Z, ZV),
	getValue(X, XV),
	getValue(Y, YV),
	evalNode(Op, [ZV, XV, YV], [NewZ, NewX, NewY]),
%	traceIntOp_(Op, [Z, X, Y], [ZV, XV, YV], [NewZ, NewX, NewY]),
	CurAgenda = [node(Op,Z,X,Y)|Agenda], % note: Node still on current Agenda
	updateValue_(ZV, NewZ, Z, CurAgenda),
	updateValue_(XV, NewX, X, CurAgenda),
	updateValue_(YV, NewY, Y, CurAgenda),
	stable_(Agenda).
	
stable_([node(Op,Z,X)|Agenda]) :-      % binary relation
	getValue(Z, ZV),
	getValue(X, XV),
	evalNode(Op, [ZV, XV], [NewZ, NewX]),
%	traceIntOp_(Op, [Z, X], [ZV, XV], [NewZ, NewX]),
	CurAgenda = [node(Op,Z,X)|Agenda],  % note: Node still on current Agenda
	updateValue_(ZV, NewZ, Z, CurAgenda),
	updateValue_(XV, NewX, X, CurAgenda),
	stable_(Agenda).
	
%
%  trace debug code only
%
traceIntOp_(Op, Ints, Ins, Outs) :-
	write('node:  '),write(Op),write('('),
	traceInts(Ints),
	traceChanges(Ints, Ins, Outs),
	write('\n'),!.
	
traceInts([Int]) :- print(Int),write(')').
traceInts([Int|Ints]) :- print(Int),write(','),traceInts(Ints).

traceChanges([_Int], [In], [In]).  % no change
traceChanges([Int], [_],  [Out]) :-
	write('\n    '), print(Int), write(' <- '), write(Out).
traceChanges([Int|Ints], [In|Ins], [Out|Outs]) :-
	traceChanges([Int], [In], [Out]),
	traceChanges(Ints, Ins, Outs).

	
updateValue_(Old, Old, _, _) :- !.                 % no change in value
updateValue_(_Old, New, Int, Agenda) :-            % set value to New
	putValue_(New, Int, NL),                       % update value
	broadcast_(New, Int, NL, Agenda).              % broadcast to affected nodelist
	
broadcast_([Pt,Pt], Int, _NL, Agenda) :- !,
	ismember(Agenda,node(instantiate, Int, Pt)).   % mark for instantiation, constraints run then
broadcast_(_New, _Int, NL, Agenda) :-
	subset_(NL, Agenda).                           % add constraints to agenda for execution

subset_(Xs, _) :- var(Xs),!.   % end of indefinite input list
subset_([X|Xs], List) :-
	ismember(List, X),         % checks for duplicates
	subset_(Xs, List).

ismember([X|_Xs],N) :- N==X, !.             % be careful not to trigger unification inside nodes
ismember([X|_Xs],N) :- var(X), !, X=N.      % end of indefinite list
ismember([_|Xs],N) :- ismember(Xs,N).

%
% Current values are stored in GNUP/SWI global storage, which is backtrackable
%

% get current value
getValue(Num, [Num,Num]) :-
	number(Num), !.                   % numeric value
getValue(Int, V) :-                   % assume still an interval
	interval_object(Int, _Type, Id, _NL),
	b_getval(Id,V).      %%%SWI global read 
	
putValue_([L,H], Int, NL) :-
	interval_object(Int, _Type, Id, NL), !,
	L=<H,
	b_setval(Id,[L,H]).  %%%SWI global link (backtrackable)


:- include(ia_utilities).


% end of reset chain succeeds. Need cut since predicate is discontiguous.
clpStatistics :- !.

:- initialization(clpStatistics).

