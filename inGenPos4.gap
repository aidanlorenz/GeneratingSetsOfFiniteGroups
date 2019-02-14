inGenPos4 := function(quadruple)
	# This function takes in a quadruple of maximal subgroups of PSL(2,p) and returns true if those which are in general position. This program was designed to be used in 		# conjunction with PSLMax(p) (Nachman). Written by Aidan Lorenz.

	local int12, int13, int14, int23, int24, int34;
	
	int123 := Intersection(quadruple[1], quadruple[2], quadruple[3]);
	int124 := Intersection(quadruple[1], quadruple[2], quadruple[4]);
	int134 := Intersection(quadruple[1], quadruple[3], quadruple[4]);
	int234 := Intersection(quadruple[2], quadruple[3], quadruple[4]);
	
	if not(IsSubset(triple[1], int234)) then
		if not(IsSubset(triple[2], int134)) then
			if not(IsSubset(triple[3], int124)) then
				if not(IsSubset(triple[4], int123)) then
					return true;
				fi;
			fi;
		fi;
	fi;

	return false;

end;