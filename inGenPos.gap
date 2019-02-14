inGenPos := function(triple)
	# This program takes in a triple of maximal subgroups of PSL(2,p) and returns true if those which are in general position. This program was designed to be used in 		# conjunction with PSLMax(p) (Nachman) and subsetsSize3(set) (Lorenz). Namely, the triple must be the output of subsetsSize3(PSLMax(p))[i] for some prime p.

	local int13, int23, int12;
	
	int13 := Intersection(triple[1][1], triple[3][1]);
	int23 := Intersection(triple[2][1], triple[3][1]);
	int12 := Intersection(triple[1][1], triple[2][1]);

	if not(IsSubgroup(triple[1][1], int23)) then
		if not(IsSubgroup(triple[2][1], int13)) then
			if not(IsSubgroup(triple[3][1], int12)) then
				return true;
			else
				return false;
			fi;
		else
			return false;
		fi;
	else
		return false;

end;


# NOT CURRENTLY WORKING
# To test:
# gap> results = [];
# gap> for i in [1 .. Size(subsetsSize3(PSLMax(3)))] do
# > triple := subsetsSize3(PSLMax(3))[i];
# > Add(results, inGenPos(triple));
# > od;
# gap> results;