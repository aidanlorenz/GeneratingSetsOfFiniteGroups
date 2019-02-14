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

##############################################################################

inGenPos := function(triple)
	# This function takes in a triple of maximal subgroups of PSL(2,p) and returns true if those which are in general position. This program was designed to be used in 		# conjunction with PSLMax(p) (Nachman). Namely, the triple must be the output of Combinations(PSLMax(p), 3) for some prime p. (notice there are slight differences between
	# this function and inGenPos in PSLRP.gap due to the slight difference in input format).

	local int13, int23, int12;
	
	int13 := Intersection(triple[1], triple[3]);
	int23 := Intersection(triple[2], triple[3]);
	int12 := Intersection(triple[1], triple[2]);

	if not(IsSubset(triple[1], int23)) then
		if not(IsSubset(triple[2], int13)) then
			if not(IsSubset(triple[3], int12)) then
				return true;
			fi;
		fi;
	fi;

	return false;

end;

##############################################################################

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

##############################################################################

PSLRPv5 := function(p)
	# This function takes in a prime p. It first finds all conjugacy classes containing elements of prime order. Next, looping over all such conjugacy classes, it picks a 		# representative from each conjugacy class and stores it. It then calculates all triples of maximal subgroups of PSL(2,p) which are in general position which also contain 	# the representative of the conjugacy class by combining the functions PSLMax, Combinations, and genPosList. Combinations(PSLMax(p), 3). It then checks if the intersection 	# of any three maximal subgroups in general position is trivial. If it is trivial for all triples of maximal subgroups in general position containing representatives of 	# conjugacy classes of elements of prime order, then the replacement property holds, as per a result from R. K. Dennis and Dan Collins (and the fact that the set of 		# witnesses to failure is characteristic - the prime order part I still need to think about). Thus, the output of the function is true if PSLRP satisfies the replacement 	# property for the given input data and false otherwise.

	local G, rep, maximals, max, max3s, genPos, cl, maxWithRep, triple, primeOrds, toTest, test, conjClassesPrimeOrd, primeOrd, class;

	G := PSL(2,p);
	maximals := PSLMax(p);
	toTest := [];

	conjClassesPrimeOrd := Filtered(ConjugacyClasses(G), class -> IsPrimeInt(Order(Representative(class))));

	for cl in conjClassesPrimeOrd do
		Add(toTest, Representative(cl));
	od;

	for test in toTest do

		maxWithRep := [];
		for max in maximals do
			if test in max[1] then
				Add(maxWithRep, max[1]);
			fi;
		od;

		max3s := Combinations(maxWithRep, 3);
		genPos := Filtered(max3s, inGenPos);

		for triple in genPos do
			if IsNonTrivial(Intersection(triple[1], triple[2], triple[3])) then
				#Print(rep, " fails the replacement property. \n");
				return false;
			fi;
		od;
	od;

	return true;

end;