PSLMax:=function(p)
    # This program returns all of the maximal subgroups of PSL(2,p) via Dickson's Theorem (written by Benjamin Nachman).
    local G,D,H,h,A,Q,out,q;
    G:=PSL(2,p); 
    out:=[];
    #Note that each element of out is of the form [Group,"StructureDescription"]

    #First, get the max subgroups iso to D_{p-1}  
    if (p>12) then                    
      D:=DihedralGroup(p-1);             
      H:=IsomorphicSubgroups(G,D);   
      for h in H do      
        A:=Image(h);            
        Q:=RightCosets(G,A);
        for q in Q do
          Append(out,[[A^Representative(q),"D_{p-1}"]]);
        od;
      od;
    fi;

    #Second, get the max subgroups iso to D_{p+1}
    if (not (p=7 or p=9)) then  
      D:=DihedralGroup(p+1);
      H:=IsomorphicSubgroups(G,D);
      for h in H do
        A:=Image(h);
        Q:=RightCosets(G,A);
        for q in Q do
          Append(out,[[A^Representative(q),"D_{p+1}"]]);
        od;
      od;
    fi;

    #Third, get the max subgroups iso to Z_p semi Z_{(p-1)/2}
    D:=Representative(ConjugacyClassesMaximalSubgroups(AutomorphismGroup(DihedralGroup(2*p)))[1]); 
    H:=IsomorphicSubgroups(G,D);
    for h in H do
      A:=Image(h);
      Q:=RightCosets(G,A);
      for q in Q do
          Append(out,[[A^Representative(q),"Z_p semi Z_{(p-1)/2}"]]);
      od;
    od;

    #Fourth, get the max subgroups iso to A5
    if (p mod 10 = 1 or p mod 10 = 9) then
      D:=AlternatingGroup(5);
      H:=IsomorphicSubgroups(G,D);
      for h in H do
        A:=Image(h);
        Q:=RightCosets(G,A);
        for q in Q do
          Append(out,[[A^Representative(q),"A5"]]);
        od;
      od;
    fi;

    #Fifth, get the max subgroups iso to A4
    if ((p mod 8 = 3 or p mod 8 = 5) and not(p mod 10 = 1 or p mod 10 = 9)) then
      D:=AlternatingGroup(4);
      H:=IsomorphicSubgroups(G,D);
      for h in H do
        A:=Image(h);
        Q:=RightCosets(G,A);
        for q in Q do
          Append(out,[[A^Representative(q),"A4"]]);
        od;
      od;
    fi;

    #Finally, get the max subgroups iso to S4
    if (p mod 8 = 1 or p mod 8 = 7) then
      D:=SymmetricGroup(4);
      H:=IsomorphicSubgroups(G,D);
      for h in H do
        A:=Image(h);
        Q:=RightCosets(G,A);
        for q in Q do
          Append(out,[[A^Representative(q),"S4"]]);
        od;
      od;
    fi;

    return out;

end;

########################################################

maxWithRep := function()



end;

########################################################

inGenPos := function(triple)
	# This function takes in a triple of maximal subgroups of PSL(2,p) and returns true if those which are in general position. This program was designed to be used in 		# conjunction with PSLMax(p) (Nachman). Namely, the triple must be the output of Combinations(PSLMax(p), 3) for some prime p.

	local int13, int23, int12;
	
	int13 := Intersection(triple[1][1], triple[3][1]);
	int23 := Intersection(triple[2][1], triple[3][1]);
	int12 := Intersection(triple[1][1], triple[2][1]);

	if not(IsSubset(triple[1][1], int23)) then
		if not(IsSubset(triple[2][1], int13)) then
			if not(IsSubset(triple[3][1], int12)) then
				return true;
			else
				return false;
			fi;
		else
			return false;
		fi;
	else
		return false;
	fi;

end;

########################################################

inGenPos_4 := function(quadruple)
	# This function takes in a quadruple of maximal subgroups of PSL(2,p) and returns true if those which are in general position. This program was designed to be used in 		# conjunction with PSLMax(p) (Nachman). Namely, the triple must be the output of Combinations(PSLMax(p), 4) for some prime p.

	local int234, int134, int124, int123;
	
	int234 := Intersection(quadruple[2][1], quadruple[3][1], quadruple[4][1]);
	int134 := Intersection(quadruple[1][1], quadruple[3][1], quadruple[4][1]);
	int124 := Intersection(quadruple[1][1], quadruple[2][1], quadruple[4][1]);
	int123 := Intersection(quadruple[1][1], quadruple[2][1], quadruple[3][1]);

	if not(IsSubset(quadruple[1][1], int234)) then
		if not(IsSubset(quadruple[2][1], int134)) then
			if not(IsSubset(quadruple[3][1], int124)) then
				if not(IsSubset(quadruple[4][1], int123)) then
					return true;
				else
					return false;
				fi;
			else
				return false;
			fi;
		else
			return false;
		fi;
	else
		return false;
	fi;

end;

########################################################

genPosList := function(max3s)
	# This function takes in a list of triples of maximal subgroups of PSL(2,p) for some prime p. It returns the sublist of those triples which are in general position.

	local genPos, triple;
	
	genPos := [];
	
	for triple in max3s do
		if inGenPos(triple) then
			Add(genPos, triple);
		fi;
	od;

	return genPos;
end;

########################################################

genPosList_4 := function(max4s)
	# This function takes in a list of quadruples of maximal subgroups of PSL(2,p) for some prime p (7, 11, 19, or 31). It returns the sublist of those triples which are in 	# general position.

	local genPos, quadruple;
	
	genPos := [];
	
	for quadruple in max4s do
		if inGenPos_4(quadruple) then
			Add(genPos, quadruple);
		fi;
	od;

	return genPos;
end;

########################################################

PSLRP := function(genPos)
	# This function takes in triples of maximal subgroups in general position (to be obtained using PSLMax(p), subsetsSize3(set), and inGenPos(triple)). It then checks
	# if there intersection is trivial or not. If it is trivial for all triples of maximal subgroups in general position, then the replacement property hold, as per
	# a result from R. K. Dennis and Dan Collins. Thus, the output of the function is true if PSLRP satisfies the replacement property for the given input data and 
	# false otherwise.

	local triple;
	
	for triple in genPos do
		if IsNonTrivial(Intersection(triple[1][1], triple[2][1], triple[3][1])) then
			return false;
		fi;
	od;
	
	return true;

end;

########################################################

PSLRP2 := function(p)
	# This function takes in a prime p. It first calculates all triples of maximal subgroups of PSL(2,p) which are in general position by combining the functions PSLMax, 
	# Combinations, and genPosList. Combinations(PSLMax(p), 3). It then checks if the intersection of any three maximal subgroups in general position is trivial.
	# If it is trivial for all triples of maximal subgroups in general position, then the replacement property hold, as per a result from R. K. Dennis and Dan Collins. Thus, 	# the output of the function is true if PSLRP satisfies the replacement property for the given input data and false otherwise.

	local genPos, triple;

	genPos := genPosList( Combinations( PSLMax(p), 3 ) );
	
	for triple in genPos do
		if IsNonTrivial(Intersection(triple[1][1], triple[2][1], triple[3][1])) then
			return false;
		fi;
	od;
	
	return true;
end;

########################################################

PSLRP_4 := function(genPos)
	# This function takes in quadruples of maximal subgroups in general position (to be obtained using PSLMax(p), Combinations, and inGenPos(quadruple)). It then checks
	# if there intersection is trivial or not. If it is trivial for all quadruples of maximal subgroups in general position, then the replacement property holds, as per
	# a result from R. K. Dennis and Dan Collins. Thus, the output of the function is true if PSLRP satisfies the replacement property for the given input data and 
	# false otherwise.

	local quadruple;
	
	for quadruple in genPos do
		if IsNonTrivial(Intersection(quadruple[1][1], quadruple[2][1], quadruple[3][1], quadruple[4][1])) then
			return false;
		fi;
	od;
	
	return true;

end;

########################################################

PSLRP2_4 := function(p)
	# This function takes in a prime p (must be 7, 11, 19, or 31). It first calculates all triples of maximal subgroups of PSL(2,p) which are in general position by combining 	# the functions PSLMax, Combinations, and genPosList. Combinations(PSLMax(p), 3). It then checks if the intersection of any three maximal subgroups in general position is 	# trivial. If it is trivial for all triples of maximal subgroups in general position, then the replacement property hold, as per a result from R. K. Dennis and Dan 		# Collins. Thus, the output of the function is true if PSLRP satisfies the replacement property for the given input data and false otherwise.

	local genPos, quadruple;

	genPos := genPosList_4( Combinations( PSLMax(p), 4 ) );
	
	for quadruple in genPos do
		if IsNonTrivial(Intersection(quadruple[1][1], quadruple[2][1], quadruple[3][1], quadruple[4][1])) then
			return false;
		fi;
	od;
	
	return true;
end;
