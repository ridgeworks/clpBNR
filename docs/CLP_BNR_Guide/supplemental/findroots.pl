% generate roots of polynomial P = f(X)
findroots(P,X) :-
	partial_derivative(P,X,D),         % must be differentiable
	% create templates for original polynomial and derivative
	copy_term([P,X],Poly),
	copy_term([D,X],Derv),
	% apply constraint f(X)=0
	{P==0},
	% generate minimum width criteria from flag
	current_prolog_flag(clpBNR_default_precision,Pr),
	Eps is 10**(-(Pr+1)),
	% taylor expansion search
	taylor_(X,Poly,Derv,Eps).

taylor_(X,Poly,Derv,Eps) :-
	% continue if interval X wider than error criteria
	range(X,[XL,XH]),                  % reached Eps limit?
	catch(XH-XL > Eps, _, true),  !,   % catch in case of overflow (limit not reached)
	% calculate simple midpoint value for X0
	X0 is XL/2+XH/2,
	apply_taylor_(X,X0,Poly,Derv),
	taylor_(X,Poly,Derv,Eps).          % rinse and repeat
taylor_(X,Poly,Derv,Eps).              % based on Eps, X is too small to split

apply_taylor_(X,X0,Poly,Derv) :-
	% symbolically apply function
	copy_term(Poly,[FX0,X0]),          %  f(X0) = FX0
	copy_term(Derv,[DXi,Xi]),          % f'(Xi) = DXi
	% Taylor expansion constraints
	{0 == FX0 + (X-pt(X0)) * DXi},
	({X =< Xi, Xi =< pt(X0)} ; {pt(X0) =< Xi, Xi =< X}).
