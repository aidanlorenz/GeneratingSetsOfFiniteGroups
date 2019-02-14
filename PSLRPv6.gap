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
ordFail := 0; #This initializes ordFail as a global variable. YOU CAN IGNORE ERROR WARNINGS FOR UNDEFINED GLOBAL VARIABLE WHEN LOADING THIS FILE!

PSLRPv6 := function(p)
	# This function takes in a prime p. It first finds all conjugacy classes (conjugacy classes because the set of witnesses to failure is characteristic) containing elements of 	# prime order, picks a representative from each and stores it (this is because witnesses to failure always have prime order - or at least is suffices to check only elements 	# of prime order. Not sure why). Then looping over all those representatives, it calculates all triples of maximal subgroups of PSL(2,p) containing that representative. 	# Next, we generate all combinations of 3 of said maximal subgroups and check if each of those triples are in general position. If any are in general position, then we can 	# conclude the replacement property does not hold. This is because we know that those three maximal subgroups in general position will not have trivial intersection (they 	# all contain the representative) and thus, by a result of R. K. Dennis and Dan Collins, the group fails the replacement property. If, for all the representatives, there are 	# no triples in general position, then they all must have trivial intersection and hence the replacement property is satisfied. Written by Aidan Lorenz.

	# VERSION 6 IS THE BEST VERSION TO DATE (6/21/18)
	
	local G, conjClasses, rep, maximals, max, max3s, genPos, cl, maxWithRep, triple, primeOrds, toTest, test;

	G := PSL(2,p);
	conjClasses := ConjugacyClasses(G);
	maximals := PSLMax(p);
	toTest := [];

	for cl in conjClasses do
		rep := Representative(cl);
		if IsPrimeInt(Order(rep)) then
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
				#Print(test, " is a witness to failure. It has order: ", Order(test), " "); # Uncomment this line to see the failing element.
				ordFail := Order(test);;
				return false;
			fi;
		od;
		
		ordFail := "-";
	od;

	return true;
end;

##############################################################################

conjecture := function(p)
	# This function gives the conjectured (Nachman) answer as to whether or not PSL(2,p) satisfies the replacement property for a given prime p. Written by Aidan Lorenz.
	local mod8, mod10;
	
	if 1 = p mod 8 then
		mod8 := 1;
	fi;

	if 7 = p mod 8 then
		mod8 := -1;
	fi;
	
	if 1 = p mod 10 then
		mod10 := 1;
	fi;
	
	if 9 = p mod 10 then
		mod10 := -1;
	fi;

	if 3 = p mod 8 then
		mod8 := 3;
	fi;
	
	if 5 = p mod 8 then
		mod8 := -3;
	fi;

	if 3 = p mod 10 then
		mod10 := 3;
	fi;
	
	if 7 = p mod 10 then
		mod10 := -3;
	fi;

	if ((mod10 = 3) or (mod10 = -3)) and ((mod8 = 3) or (mod8 = -3)) then
		return true;
	else
		return false;
	fi;

end;

##############################################################################

PSLRPv6Test := function(max)
	# This prints out the following for all primes up to max (in this order): the prime, whether or not it PSL(2,p) satisfies the replacement property (according to PSLRPv6), 	# whether or not Nachman's conjecture has it satisfying the replacement property, and - if it fails - the order of an example element that fails. THIS IS THE BEST FUNCTION
	# FOR TESTING MANY PRIMES AT ONCE. Written by Aidan Lorenz.

	local p, result;

	Print("prime  RepProp  Conject  OrdFail \n");

	for p in Primes do
		if p<max and not(p=7) and not(p=11) and not(p=19) and not(p=31) and p>5 then
			result := PSLRPv6(p);
			Print(RJust(3, p), "     ", RJust(5, result), "    ", RJust(5, conjecture(p)), "      ", ordFail, "\n");
		fi;
	od;

	return;
end;
		
##############################################################################

RJust:=function(n,x)
    # This file is only used for formatting output of PSLRPv6Test. It was taken from R.K. Dennis's file utility5.gap.

    local str,len,pad,spc,add,i,tmp,sqt;
    ## RKD
    # right justify to fill n characters when printing
    str:=String(x);
    spc:=String(" ");
    sqt:=String("'");
    spc:=List(spc,String);
    len:=Length(str);
    pad:=ShallowCopy(spc[1]);
    add:=n-len-1;
    if(n>len) then
       for i in [1..add] do
           tmp:=ShallowCopy(spc[1]);
           Append(pad,tmp);
       od;
       # remove single quotes
       RemoveCharacters(pad,sqt);
       Append(pad,str);
       str:=pad;    
    fi;
    return str; 
end;