%
% generate roots of polynomial P = f(X)
%	uses library(yall) for lambda expressions
%
findroots(P,X) :-
	% create lambdas for original polynomial and derivative
	lambda_for_(P,X,Poly),
	partial_derivative(P,X,D),         % must be differentiable
	lambda_for_(D,X,Derv),
	% apply constraint f(X)=0
	call(Poly,X,Px), {Px==0},   % f(X) = 0
	% generate minimum width criteria from flag
	current_prolog_flag(clpBNR_default_precision,Pr),
	Eps is 10**(-(Pr+1)),
	% taylor expansion search
	taylor_(X,Poly,Derv,Eps).
	
lambda_for_(Fx,X,[X,Fx]>>true).

taylor_(X,Poly,Derv,Eps) :-
	% continue if interval X wider than error criteria
	range(X,[XL,XH]),                  % reached Eps limit?
	XH-XL > Eps,  !,
	% calculate simple midpoint value for X0
	X0 is XL/2+XH/2,
	% symbolically apply function
	call(Poly,X0,FX0),                 %  f(X0) = FX0
	call(Derv,Xi,DXi),                 % f'(Xi) = DXi
	{0 == FX0 + (X-X0) * DXi},         % and constrain
	% split for search
	({X =< Xi, Xi =< X0} ; {X0 =< Xi, Xi =< X}),
	taylor_(X,Poly,Derv,Eps).          % rinse and repeat
taylor_(_X,_,_,_Eps).                  % X is too small to split based on Eps
