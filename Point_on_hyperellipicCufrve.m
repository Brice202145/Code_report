function Points_on_HyperellipticCurve(f)
A<x,y> := AffineSpace(Rationals(),2);
F:=y^2-f;
C1 := Curve(A,[F]);
// curve C is the projective model of our hyperelliptic curve
C<x,y,z> := ProjectiveClosure(C1);
//phi1 and phi2 are involutions of C
phi1 := iso<C -> C | [-x,y,z],[-x,y,z]>; 
phi2 := iso<C -> C | [-x,-y,z],[-x,-y,z]>;
// G1 and G2 are two subgroups of the group of automorphisms of C
G1 := AutomorphismGroup(C,[phi1]);
G2 := AutomorphismGroup(C,[phi2]); 
// E and H are the quotient curves of C by G1 and G2 respectively
E, m1 := CurveQuotient(G1);
H, m2 := CurveQuotient(G2);
//J is the Jacobian of H of dimension Genus(H)
J:=Jacobian(H);
//Si le rang de E n'est pas zéros alors on calcule celui de J
if RankBound(Jacobian(E)) ne 0 then
   //if the rank of J is zero we use ChabautyJ to calculate H(Q) via Chabauty0 and for any point of H uses the pullback of m2
    if RankBound(J) eq 0 then  
        RationalPoints_on_H:=Chabauty0(J);
        for i in [1..#RationalPoints_on_H] do
            RationalPoints_on_C:=RationalPoints(Difference(Pullback(m2, RationalPoints_on_H[i]), BaseScheme(m2)));
        end for; 
    // if the rank of J is 1 we use ChabautyJ to calculate H(Q) via Chabauty0 and for any point of H we use the pullback of m2
    else if RankBound(J) eq 1 then
          ptsH:=RationalPoints(H: Bound:=1000);
          for i in [2..#ptsH] do
              PJ:=J! [ptsH[i], ptsH[1]];
              if Order(PJ) eq 0 then 
                 all_ptsH:=Chabauty(PJ: ptC:=ptsH[1]);
                 for P in all_ptsH do
                     preimageofp:= P @@ m2;
                     RationalPoints_on_C:=Points(preimageofp);
                    end for;
                end if;
            end for;
    end if;
end if;
end if;
return RationalPoints_on_C;
end function; 
