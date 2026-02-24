transportation_eg(Vars, Constraints, Cost) :-
	Vars = [A1,A2,A3,B1,B2,B3,C1,C2,C3,D1,D2,D3], 
	Vars::integer(0,_),
	Constraints = {
	  A1 + A2 + A3 == 21,
	  B1 + B2 + B3 == 40,
	  C1 + C2 + C3 == 34,
	  D1 + D2 + D3 == 10,
	
	  A1 + B1 + C1 + D1 =< 50,
	  A2 + B2 + C2 + D2 =< 30,
	  A3 + B3 + C3 + D3 =< 40
	},
	Cost = 10*A1 + 7*A2 + 200*A3 + 8*B1 + 5*B2 + 10*B3 + 5*C1 + 5*C2 +  8*C3 + 9*D1 + 3*D2 +  7*D3.
