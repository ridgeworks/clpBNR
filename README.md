# CLP(BNR)
A Prolog implementation of CLP(BNR) as an SWI-Prolog module.

CLP(BNR) is a Prolog based constraint programming language based on relational interval arithmetic on the real domain; integers are a constrained subset of the reals. 

This is an alpha release with limited documentation - Use at own risk.

The package declaration is:

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

A couple of query examples - constrained interval variables are output as terms with functor `δN` where N is a unique integer value:

	?- {1==X+2*Y, Y-3*X==0}.
	X = δ1(0.14285714285714268, 0.14285714285714302),
	Y = δ2(0.42857142857142827, 0.4285714285714289).


	?- X::real(0,1), {0 == 35*X**256 - 14*X**17 + X}, solve(X).
	X = δ1(0.0, 4.1720134847010085e-308) 
	X = δ1(0.847943660827315, 0.8479436608273155) 
	X = δ1(0.9958424942004978, 0.9958424942004983).


	?- {Y**3+X**3==2*X*Y, X**2+Y**2==1},solve([X,Y]),nl,print_interval([X,Y]),fail.
	
	[[-0.9203685852369246,-0.9203685826261211],[0.391052000773532,0.39105200691824143]]
	[[0.3910519319572065,0.39105207710634754],[-0.9203686144760354,-0.9203685528041528]]
	[[0.4497872103384068,0.44978761018654057],[0.8931355472282356,0.8931357485936807]]
	[[0.8931355770724781,0.8931356990736679],[0.44978730866954364,0.449787550925335]]
	false.


To load CLP(BNR) on SWI-Prolog, consult `clpBNR.pl` (in `src/` directory) which will automatically include `ia_primitives.pl` and `ia_utilities.pl`.
