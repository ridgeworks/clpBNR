%
% integrate/5 for User Guide Examples
%
integrate(DFxy,X,Initial,Final,YDomain) :-
	current_prolog_flag(clpBNR_default_precision,Ctrl),
	integrate(DFxy,X,Initial,Final,YDomain,Ctrl).

integrate(DFxy,X,Initial,Final,YDomain,Ctrl) :-
	integrate(DFxy,X,Initial,Final,YDomain,Ctrl,_).

integrate(DFxy,X,(Xi,Yi),(Xf,Yf),YDomain,Ctrl,Out) :-
	integrateV([DFxy],X,(Xi,[Yi]),(Xf,[Yf]),[YDomain],Ctrl,Out).

/*=============================================================================*
 |  integrateV/5
 |
 | integrate([d(Y)=Fxy|Fxys], X, Initial, Final, Ydomains) % default Ctrl = clpBNR_default_precision
 | integrate([d(Y)=Fxy|Fxys], X, Initial, Final, Ydomains, Ctrl)
 | integrate([d(Y)=Fxy|Fxys], X, Initial, Final, Ydomains, Ctrl, Out) % with intermediate results
 |
 | where
 |       X is the independent variable and Y the dependent variable
 |       Fxys is a list of d(Y)=Fxy where dY/dX = Fxy (f(X,Y))
 |       Initial, Final are boundary (X,Y) values (Initial.X =< Final.X)
 |			Y is a list of Y values in same order as Fxy.Y
 |			Values may be defined by arithmetic expressions
 |       Ydomains is a list of Y domains, e.g., [real(L,U)], and bounds Y(X)
 |       Ctrl controls number of binary subdivisions (= 2**Ctrl)
 |       Out is (optional) list of X,Y pairs over interval of integration
 |
 | uses library(yall) for Lambda expressions and library(apply):maplist and exclude
 *=============================================================================*/

integrateV(DFxys,X,Initial,Final,Ydomains) :-
	current_prolog_flag(clpBNR_default_precision,Ctrl),
	integrateV(DFxys,X,Initial,Final,Ydomains,Ctrl).

integrateV(DFxys,X,Initial,Final,Ydomains,Ctrl) :-
	integrateV(DFxys,X,Initial,Final,Ydomains,Ctrl,_).

integrateV(DFxys,X,(Xi,Yis),(Xf,Yfs),Ydomains,Ctrl,Out) :-
    integer(Ctrl), Ctrl>0,           % Ctrl must be positive integer
    maplist(eval_bv,[Xi|Yis],[X0|Y0s]),
    maplist(eval_bv,[Xf|Yfs],[X1|Y1s]),
	maplist(dependent_var,DFxys,Ys),        % list of Y values in Fxy order
	maplist(fXY_lambda(X,Ys),DFxys,FxyLs),  % corresponding list of Fxy lambdas
	maplist(total_derivative_,FxyLs,Ys,DFxyLs),  % corresponding list of F derivative lambdas
	maplist(::,Y0s,Ydomains),
	maplist(::,Y1s,Ydomains),
	!,
    integrateV_(Ctrl,FxyLs,DFxyLs,(X0,Y0s),(X1,Y1s),Ydomains,Out/[(X1,Y1s)]).

eval_bv(Val,Val) :- var(Val),!.
eval_bv(Exp,Val) :- Val is Exp.

dependent_var(d(Y)=_,Y).

fXY_lambda(X,Ys,_=Fxy,FxyL) :- lambda_for_(Fxy,X,Ys,FxyL).
		
% construct Lambda for derivative function of Fxy from Lambda of Fxy
total_derivative_((_Free/Ps>>G),Y,DxyL) :- !,
	total_derivative_((Ps>>G),Y,DxyL).
total_derivative_(([X,Ys,Fxy]>>_),Y,DxyL) :-
	partial_derivative(Fxy,X,DFDX),  % clpBNR built-in
	partial_derivative(Fxy,Y,DFDY),
	td_expression(DFDX,DFDY,Fxy,DExp), !,
	lambda_for_(DExp,X,Ys,DxyL).

td_expression(DFDX,0,_,DFDX).	
td_expression(0,DFDY,Fxy,DFDY*Fxy).	
td_expression(DFDX,DFDY,Fxy,DFDX+DFDY*Fxy).	

% Create Lambda expression for Fxy
lambda_for_(Fxy,X,Y,Args>>true) :-
	term_variables(Fxy,FVs),
	(is_list(Y) -> Parms=[X|Y] ; Parms=[X,Y]),  % flatten if Y is a list
	exclude(var_member_(Parms),FVs,EVs),        % EVs = free variables
	lambda_args_(EVs,[X,Y,Fxy],Args).           % create lambda args

var_member_([L|_], E) :- L==E, !.
var_member_([_|Ls],E) :- var_member_(Ls,E).

lambda_args_(EVs,Ps,{EV}/Ps) :- comma_op_(EVs,EV), !.
lambda_args_(_,Ps,Ps).

comma_op_([X],X) :- !.
comma_op_([X|Xs],(X,Y)) :- comma_op_(Xs,Y).	


% integration loop
integrateV_(0, FxyLs, DxyLs, Initial, Final, Ydomains, [Initial|Ps]/Ps) :- !,
	% integration step
	step_trapV(FxyLs, DxyLs, Initial, Final, Ydomains).

integrateV_(Ctrl, FxyLs, DxyLs, Initial, Final, Ydomains, L/E) :-
    % create interpolation point and integrate two halves
    interpolateV_(Initial, Final, Ydomains, Middle),
    Cn is Ctrl - 1,
    integrateV_(Cn, FxyLs, DxyLs, Initial, Middle, Ydomains, L/M),
    integrateV_(Cn, FxyLs, DxyLs, Middle,  Final,  Ydomains, M/E).

interpolateV_((X0,_Y0s), (X1,_Y1s), Ydomains, (XM,YMs)) :-
    XM is (X0 + X1)/2,            % XM is midpoint of (X0,X1)
    maplist(::,YMs,Ydomains).     % corresponding YMs
	
step_trapV(FxyLs, DxyLs, (X0,Y0), (X1,Y1), Ydomains) :-
    Dx is X1 - X0,         % assumed (X1>X0)
    DX :: real(0,Dx),      % range for estimate
    X01:: real(X0,X1),     % range of X in step
    constrain_V(FxyLs,X0,Y0,F0),
    constrain_V(FxyLs,X1,Y1,F1),
	maplist(::,Y01,Ydomains),
    constrain_V(DxyLs,X01,Y01,D),
	build_constraintsV(Y0,Y1,Y01,Dx,DX,F0,F1,D,Cs),
	{Cs}.
	
constrain_V([],_X,_Ys,[]).
constrain_V([Lambda|Lambdas],X,Ys,[F|Fs]) :-
	call(Lambda,X,Ys,F),
	constrain_V(Lambdas,X,Ys,Fs).
	
build_constraintsV([],[],[],_Dx,_DX,[],[],[],[]).
build_constraintsV([Y0|Y0s],[Y1|Y1s],[Y01|Y01s],Dx,DX,[F0|F0s],[F1|F1s],[D|Ds],[
	[FM <= (F0+F1)/2,
	 R <= D, 8*DR + R == RP, RP == R,
	 Y01 - Y0 == DX*(FM + DR*DX),
     Y1  - Y0 == Dx*(FM + DR*Dx)
	]
	|Cs]) :-
	build_constraintsV(Y0s,Y1s,Y01s,Dx,DX,F0s,F1s,Ds,Cs).
