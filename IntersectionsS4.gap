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

IntersectionsS4 := function(p)
	# This functions finds maximal subgroups of PSL(2,p) which are isomorphic to S4. It then looks at the isomorphism type of all the pairwise intersections of those maximal 	# subgroups. The hope is that for each prime, there will always be one such intersection isomorphic to S3 (in which case the function returns true). Otherwise, the function 	# returns false.

	local maximals, max, int, S4s, i, j;

	maximals := PSLMax(p);
	S4s := [];

	for max in maximals do
		if StructureDescription(max[1]) = "S4" then
			Add(S4s, max[1]);
		fi;
	od;

	for i in [1 .. Size(S4s)] do
		for j in [i+1 .. Size(S4s)] do
			int := Intersection(S4s[i], S4s[j]);
			if StructureDescription(int) = "S3" then
				return true;
			fi;
		od;
	od;

	return false;

end;

##############################################################################

TestIntS4 := function(max)
	# To test IntersectionsS4.

	local p;

	for p in Primes do
		if (p<max) and (p > 7) and ((p mod 8 = 1) or (p mod 8 = 7)) then
			Print(p, ": ", IntersectionsS4(p), "\n");
		fi;
	od;

	return;

end;

##############################################################################

ConjIntS4 := function(p)
	#This program finds maximal subgroups of PSL(2,p) which are isomorphic to S4. It then intersects such subgroups with its conjugates and looks at the isomorphism types of 	# those intersections. This program is very inefficient, as it never really made it past being a bud of an idea.
	
	local G, maximals, list, max, g, int, S4s, S4;

	G := PSL(2,p);
	maximals := PSLMax(p);
	list := [];
	S4s := [];

	for max in maximals do
		if StructureDescription(max[1]) = "S4" then
			Add(S4s, max[1]);
		fi;
	od;

	for S4 in S4s do
		for g in G do
				int := Intersection(S4, ConjugateGroup(S4, g));
				if not(StructureDescription(int) in list) then
					Add(list, StructureDescription(int));
				fi;
		od;
	od;

	return list;

end;
		
##############################################################################

ConjIntS4Test := function(max)
	# To test ConjIntS4.

	local p;

	for p in Primes do
		if (p<max) and ((7 = p mod 8) or (1 = p mod 8)) and (p>7) then
			Print(p, ": ", ConjIntS4(p));
		fi;
	od;

	return;

end;

