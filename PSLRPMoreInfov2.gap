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
	# this function and inGenPos in PSLRP.gap due to the slight difference in input format). Written by Aidan Lorenz.

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

PSLRPMorev2 := function(p)
	# This function takes in a prime p. It first finds all conjugacy classes (conjugacy classes because the set of witnesses to failure is characteristic) containing elements of 	# prime order 2 or 3 (it can be shown that these are the only possibilities for orders of witnesses to failure), picks a representative from each and stores it (this is 	# because if there is a witness to failure, then there is one with prime order). Then looping over all those representatives, it calculates all triples of maximal subgroups 	# of PSL(2,p) containing that representative. Next, we generate all combinations of 3 of said maximal subgroups and check if each of those triples are in general position. 	# If any are in general position, then we check to make sure that there is an irredundant generating sequence corresponding to that triple. If there is, we can conclude the 	# replacement property does not hold. This is because we know that those three maximal subgroups in general position will not have trivial intersection (they all contain the 	# representative) and thus, by a result of R. K. Dennis and Dan Collins, the group fails the replacement property. If, for all the representatives, there are no triples in 	# general position, then they all must have trivial intersection and hence the replacement property is satisfied. Written by Aidan Lorenz.
	
	local G,conjClasses,rep,maximals,max,max3s,genPos,cl,maxWithRep,triple,toTest,test,int1,int2,int3,R,int1MinusR,int2MinusR,int3MinusR,output,count,x,y,z,outs;

	G := PSL(2,p);
	conjClasses := ConjugacyClasses(G);
	maximals := PSLMax(p);
	toTest := [];
	outs := [];
	count := 0;

	for cl in conjClasses do
		rep := Representative(cl);
		if Order(rep)=3 or Order(rep)=2 then
			Add(toTest, rep);
		fi;
	od;

	SortBy(toTest, Order); # This is done simply because witnesses to failure typically have orders either 2 or 3 (at least all known examples do)

	for test in toTest do

		maxWithRep := [];
		for max in maximals do
			if test in max[1] then
				Add(maxWithRep, max[1]);
			fi;
		od;

		max3s := Combinations(maxWithRep, 3);
		
		for triple in max3s do
			if inGenPos(triple) then
				count := count + 1;
				int1 := Intersection(triple[2], triple[3]);
				int2 := Intersection(triple[1], triple[3]);
				int3 := Intersection(triple[1], triple[2]);
				R := Intersection(triple[1], triple[2], triple[3]);
	
				int1MinusR := Filtered(int1, x -> not(x in R));
				int2MinusR := Filtered(int2, x -> not(x in R));
				int3MinusR := Filtered(int3, x -> not(x in R));

				for x in int1MinusR do
					for y in int2MinusR do
						for z in int3MinusR do
							if Group(x,y,z) = G then
								output := [StructureDescription(R), [StructureDescription(int1), StructureDescription(int2), StructureDescription(int3)], [StructureDescription(triple[1]), StructureDescription(triple[2]), StructureDescription(triple[3])]];

								if not(output in outs) then
									Add(outs, output);
								fi;

							fi;
						od;
					od;
				od;
			fi;
		od;
	od;

	Add(outs, count);

	return outs;

end;
