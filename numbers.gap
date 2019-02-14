numbers := function(p)

	local x, y, z, first, second, possibles, i, j, max;

	possibles := [];
	max := 300;

	if (p mod 8 = 1) or (p mod 8 = 7) then
		for x in [1 .. max] do
			for y in [1 .. max] do
				for z in [1 .. max] do
					first := x^(2) + y*z;
					second := (z-x-y)^(2);
					
					if (first mod p = p-1) and (second mod p = 2) then
						Add(possibles, [x,y,z]);
					fi;
				od;
			od;
		od;
	fi;

	for i in [1 .. Size(possibles)] do
		for j in [i+1 .. Size(possibles)] do
			if possibles[i][1] + possibles[i][3] = possibles[j][1] + possibles[j][3] then
				if possibles[i][2] - possibles[i][1] = possibles[j][2] - possibles[j][1] then
					if -2*possibles[i][1] - possibles[i][2] = -2*possibles[j][1] - possibles[j][2] then
						return [i, j];
					fi;
				fi;
			fi;
		od;
	od;


	return "out";

end;

##################################

numbers2 := function(p, max)

	local possiblesX, possiblesY, possiblesZ, i, j, k, x, y, z, check1, check2, check3, outs, unfiltered, filtered, hopeful, solutions;

	possiblesX := [];
	possiblesY := [];
	possiblesZ := [];
	outs := [];
	solutions := [];

	if not( (p mod 8 = 1) or (p mod 8 = 7) ) then
		return "p must be +/- 1 mod 8";
	fi;

	for i in [-max .. max] do
		for j in [-max .. max] do
			for k in [-max .. max] do
				if (i^2 + j*k mod p = p-1) then
					Add(possiblesX, [i, j, k]);
					Add(possiblesY, [i, j, k]);
					Add(possiblesZ, [i, j, k]);
				fi;
			od;
		od;
	od;

	for x in possiblesX do
		for y in possiblesY do
			for z in possiblesZ do
				check1 := 2*x[1]*y[1] + x[2]*y[3] + x[3]*y[2] mod p;
				check2 := 2*y[1]*z[1] + y[2]*z[3] + y[3]*z[2] mod p;
				check3 := 2*x[1]*z[1] + x[2]*z[3] + x[3]*z[2] mod p;
				if ( (check1 = 1) or (check1 = p-1) ) then
					if ( (check2 = 1) or (check2 = p-1) ) then
						if check3 = 0 then
							Add(outs, [x, y, z]);
						fi;
					fi;
				fi;
			od;
		od;
	od;

	unfiltered := Combinations(outs, 2);
	filtered := Filtered(unfiltered, x -> (x[1][1] = x[2][1]) and (x[1][2] = x[2][2]));

	for hopeful in filtered do
		if not(hopeful[1][3] = hopeful[2][3]) then
			Add(solutions, hopeful);
		fi;
	od;

	return solutions;
end;
			
	