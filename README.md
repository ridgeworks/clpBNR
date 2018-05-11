# CLP(BNR)
A Prolog implementation of CLP(BNR) as a package for SWI-Prolog.

CLP(BNR) is a Prolog based constraint programming language based on relation interval arithmetic on integer and real domains.

This is an alpha release with limited documentation - Use at own risk.

Source can be found in the `src` directory.

To load, consult `clpBNR.pl`. The package declaration is:

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

A couple of query examples:

	?- {1==X+2*Y, Y-3*X==0}, print_interval([X,Y]).
	[[0.14285714285714268,0.14285714285714302],[0.42857142857142827,0.4285714285714289]]


	?- X::real(0,1), {0 == 35*X**256 - 14*X**17 + X}, solve(X), print_interval(X).
	[0,3.8938792523876054e-308] ;
	[0.8479436608273149,0.8479436608273156] ;
	[0.9958424942004978,0.9958424942004983]


	?- {Y**3+X**3==2*X*Y, X**2+Y**2==1},solve([X,Y]),nl,print_interval([X,Y]),fail.
	
	[[-0.9203685852369246,-0.920368582626121],[0.39105200077353214,0.39105200691824155]]
	[[0.3910519319572066,0.39105207710634765],[-0.9203686144760354,-0.9203685528041526]]
	[[0.44978721033840646,0.4497876101865405],[0.8931355472282356,0.893135748593681]]
	[[0.8931355770724779,0.8931356990736684],[0.44978730866954264,0.4497875509253353]]
	false.
