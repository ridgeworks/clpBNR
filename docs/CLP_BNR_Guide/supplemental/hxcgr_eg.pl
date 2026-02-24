% Example 2.1, COMPUTATIONAL RESULTS FOR AN EFFICIENT IMPLEMENTATION OF THE GOP ALGORITHM AND ITS VARIANTS
%
% https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=69e4d649abfc067107b1b871f54b6aa8151a506c
%

hxcgr_eg(temps([T11,T12,T21,T22],Ti1,To1,Ti2,To2),flows(Fi1,Fi2,FB12,FB21,Fo1,Fo2,FE1,FE2),OF,Cs,CostF) :-
	Cs = [
	T11 == 500-To1, T11>=10,
	T12 == 250-Ti1, T12>=10,
	T21 == 350-To2, T21>=10,
	T22 == 200-Ti2, T22>=10,
	Ti1 >= 150, Ti2 >= 150,   % minimum temperature based on input stream
	FE1 =< 10, FE2 =< 10,     % maximum flow based on input stream
	% all flows positive
	0 =< Fi1, 0 =< Fi2, 0 =< FB12, 0 =< FB21, 0 =< Fo1, 0 =< Fo2, 0 =< FE1, 0 =< FE2,
	% energy balances
	FE2*(To2-Ti2) == 600,
	FE1*(To1-Ti1) == 1000,
	150*Fi1 + To2*FB12 - Ti1*FE1 == 0,
	150*Fi2 + To1*FB21 - Ti2*FE2 == 0,
	To1*Fo1 + To2*Fo2 == 3100,
	% flow balances
	Fi1 + Fi2 == 10,
	Fo1 + Fo2 == 10,
	Fo2 + FB12 == FE2,
	Fo1 + FB21 == FE1,
	Fi1 + FB12 == FE1,
	Fi2 + FB21 == FE2
	],
	OF = (1/(1r5*sqrt(T11*T12) + (T11+T12))) + (1/(1r5*sqrt(T21*T22) + (T21+T22))),
	CostF = 1300*(1000/(0.05*2r3*sqrt(T11*T12) + 1r6*(T11+T12)))**0.6 + 1300*(600/(0.05*2r3*sqrt(T21*T22) + 1r6*(T21+T22)))**0.6.

/* For example,
	?- _Ts = [T11,T12,T21,T22], hxcgr_eg(temps(_Ts,Ti1,To1,Ti2,To2),_Flows,OF,_Cs,CostF), {_Cs}, global_minimum(OF,Z), {Cost==CostF}, solve(_Ts), _Flows=..[flows,Fi1,Fi2,FB12,FB21,Fo1,Fo2,FE1,FE2].
 */