AddAttribute( RngMPol, "isIdealOfGreenRing" );
AddAttribute( RngMPol, "greenRingOfGroup" );
AddAttribute( RngMPol, "coefficientRingOfGreenRing" );
AddAttribute( RngMPol, "greenRingAsFiniteDimensionalAlgebra" );
AddAttribute( RngMPol, "embeddingsOfGreenRingAsFiniteDimensionalAlgebra" );
AddAttribute( RngMPol, "generalJacobian" );
AddAttribute( RngMPol, "cyclotomicPolynomial" );
AddAttribute( RngMPol, "polynomialRing" );

/* The following extensions of the object RngMPol apply for ideals that
   correspond to prime ideals of R(G). */
    
AddAttribute( RngMPol, "isSingularity" );
AddAttribute( RngMPol, "prime" );
AddAttribute( RngMPol, "jacobian" );
AddAttribute( RngMPol, "residualField" );
AddAttribute( RngMPol, "projectionToResidualField" );
AddAttribute( RngMPol, "projectionToQuotient" );
AddAttribute( RngMPol, "embeddingDimension" );
AddAttribute( RngMPol, "idealOfGreenRing" );
AddAttribute( RngMPol, "polynomial" );
AddAttribute( RngMPol, "prime" );

PRegularPUnipotentDecomposition := function( g, p )
    
    o := Order( g );
    d := 0;
    
    o0 := o;
    while o0 mod p eq 0 do
        o0 := o0 div p;
        d := d+1;
    end while;
    
    po := p^d;
    ro := o div po;
    
    assert po*ro eq o and ro mod p ne 0;
    
    gp := g^ro;
    gr := g^po;
    
    _ := exists(t){ <x1,x2> : x1 in sub< Universe( {g} ) | gr >,
                 x2 in sub< Universe( {g} ) | gp > | g eq x1*x2};
    
    return t[1], t[2];
end function;
    
PSingularClasses := function( g, p )
    
    reps := [ x[3] : x in ConjugacyClasses( g )];
    cm := ClassMap( g );
    repsreg := [ PRegularPUnipotentDecomposition( x, p  )@cm : x in reps ];
    
    inds := [ y : y in [1..#reps] | #[ x : x in repsreg | x eq y ] gt 1];
    
    return inds;
end function;
    
IdealOfGreenRingAsPolynomialRing := function( G )
    
    // set up some variables
      
    irr := CharacterTable( G );
    deg := #irr;
    P := PolynomialRing( Integers(), deg );
    AssignNames( ~P, [ "c" cat Sprint( i ) : i in [1..deg-1]] cat [ "x" ] );
    /* gens is the generators of the pol ring that correspond to 
       characters x_1,..,x_k, plus the generator that corresponds to xi. */
    gens := [ One( P )] cat [ P.i : i in [1..deg]];
    
    gensI := [];
    
    /* we calculate decompositions of x_i*x_j and set up the multplication
       table */
    
    for i in [2..deg] do
        for j in [i..deg] do
            dec := Decomposition( irr, irr[i]*irr[j] );
            Append( ~gensI, gens[i]*gens[j]-
                             &+[ Integers()!dec[k]*gens[k] : k in [1..#dec]] );
        end for; 
    end for;
    
    // add the last relation to make sure that xi is |G|-th root of unity.
    
    gensI := gensI cat [ Evaluate( CyclotomicPolynomial( #G ), gens[deg+1] )];
    I := Ideal( gensI );                   
    
    // set up some structure for I
    
    B := GroebnerBasis( I );
    J := [];
    // calculate the Jacobian matrix over Z[x_1,...,x_k,xi]
    for i in [1..#gensI-1] do
        for j in [1..deg-1] do
            Append( ~J, Derivative( gensI[i], j ));
        end for;
    end for;
    
    J := Matrix( #gensI-1, deg-1, J );
                 
    // we store some additional info in the record components of I             
                 
    cycpol := CyclotomicPolynomial( #G );
    degcyc := Degree( cycpol );
    coeff := Coefficients( cycpol );
    coeff := coeff cat [ 0 : i in [1..degcyc+1-#coeff]];
    P0<X> := PolynomialRing( Integers(), 1 );
    cycpol := &+[ Coefficients( cycpol )[i+1]*X^(degcyc-i) : 
                  i in [0..Degree( cycpol )]];
    I0 := Ideal( cycpol );
    R := P0/I0;                  
    
    I`generalJacobian := J;
    I`greenRingOfGroup := G;
    I`cyclotomicPolynomial := cycpol;
    I`coefficientRingOfGreenRing := R;
    I`isIdealOfGreenRing := true;
    I`polynomialRing := P;
    
    return I;
end function;
    
    
FactorizationOfCyclotomicPolynomialModp := function( n, p )
    
    P<x> := PolynomialRing( GF( p ));
    coeffs := Eltseq( CyclotomicPolynomial( n ));
    
    return Factorisation( &+[ coeffs[i]*x^(i-1) : i in [1..#coeffs]]);
end function;
    
PrimeIdealOfGreenRing := function( I, c, p, pol )
    
    P := Parent( I.1 );
    rk := Rank( P );
    xi := P.rk;
    G := I`greenRingOfGroup;
    F := CyclotomicField( #G );
    F0 := ext< GF( p ) | pol >;
    
    funcFF0 := function( x )
        
        coeff := Eltseq( x );
        return &+[ coeff[i]*F0.1^(i-1) : i in [1..#coeff]];
    end function;
            
    fFF0 := map< F->F0 | x:->funcFF0(x)>;
            
    T := CharacterTable( I`greenRingOfGroup );
    polc := Eltseq( pol );
    gens := [ p, &+[ (Integers())!polc[i]*xi^(i-1) : i in [1..#polc]]];
    charvals := [ F!T[i,c] : i in [1..rk]];

    for i in [1..rk-1] do
            
        coeffs := [ Integers()!x : x in Eltseq( F!T[i+1][c] )];
        gens := gens cat [ P.i-&+[ coeffs[i]*xi^(i-1) : i in [1..#coeffs]]];
    end for;
        
    funcPF := function( x )
        
        coeff, mons := CoefficientsAndMonomials( x );
        length := #coeff;
        el := 0;
        for i in [1..length] do
            exps := Exponents( mons[i] );
            el := el+coeff[i]*(&*[ charvals[j+1]^exps[j] : j in [1..#exps-1]]);
        end for;
        
        return el;
    end function;
        
    fPF := map< P->F | x:->funcPF(x)>;
    jac := I`generalJacobian;
    nrow := NumberOfRows( jac );
    ncol := NumberOfColumns( jac );
    
    mat := Matrix( F0, nrow, ncol, 
                   [[ jac[x,y]@fPF@fFF0 : y in [1..ncol]] : x in [1..nrow]]);
        
    P := Ideal( gens );
    P`jacobian := mat;
    P`prime := p;
    P`polynomial := pol;
    P`greenRingOfGroup := G;
    
    return P;
end function;
    
PrimeIdealsOfGreenRing := function( I, p )
        
    P := Parent( I.1 );
    rk := Rank( P );
    xi := P.rk;
    G := I`greenRingOfGroup;
    
    pols := [ x[1] : x in FactorizationOfCyclotomicPolynomialModp( 
                   #G, p )];
                    
                    
    return { PrimeIdealOfGreenRing( I, c, p, pol ) : c in [1..rk], 
             pol in pols };
end function;
    
SingularPrimesOfGreenRing := function( I, p )
    
    G := I`greenRingOfGroup;
    sclasses := PSingularClasses( G, p );
    pols := [ x[1] : 
              x in FactorizationOfCyclotomicPolynomialModp( #G, p )];
                          
    return [ PrimeIdealOfGreenRing( I, c, p, pol ) : c in sclasses, 
             pol in pols ];
end function;
    
    
DimensionOfZariskiTangentSpace2 := function( P : OverZ := false)
    
    J := P`jacobian;
    dim := NumberOfColumns( J ) - Rank( J );
    p := P`prime;
    n := #P`greenRingOfGroup;
    
    if not OverZ then 
        return dim;
    elif p gt 2 and n mod p eq 0 then
        return dim+1;
    elif p eq 2 and n mod 4 eq 0 then
        return dim+1;
    else
        return dim;
    end if;
    
end function;
    
EmbeddingDimension2 := function( P )
    
    p := P`prime;
    coeffs := Eltseq( P`polynomial );
    
    P0 := Parent( P.1 );
    rk := Rank( P0 );
    xi := P0.rk;
    n := #P`greenRingOfGroup;
    
    polel := &+[ (Integers()!coeffs[i])*xi^(i-1) : i in [1..#coeffs]];
    assert polel in P;
    
    if (p ne 2 and n mod p eq 0) or (n mod 4 eq 0) then 
        return DimensionOfZariskiTangentSpace2( P )+1;
    elif p in P^2 and polel in P^2 then
        print "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!";
        error(1);
        return DimensionOfZariskiTangentSpace2( P );
    else
        return DimensionOfZariskiTangentSpace2( P )+1;
    end if;
    
end function;
    
    
ComputeGroup := function( g : ToFile := false, GrpName := "" )
        
    I := IdealOfGreenRingAsPolynomialRing( g );
    n := #g;
      
    res := [* *];
    
    for p in PrimeDivisors( n ) do
        Ps := SingularPrimesOfGreenRing( I, p );
        for P in Ps do
            Append( ~res, <P`prime,P`polynomial,EmbeddingDimension2( P ),
                    DimensionOfZariskiTangentSpace2( P : OverZ := true ),
                    DimensionOfZariskiTangentSpace2( P )>);
        end for;
    end for;
        
    if not ToFile then
        return res;
    end if;
        
    
    if GrpName eq "" then
        GrpName := GroupName( g );
    end if;
    
    
    PrintFile( "file", "\\begin{table}[h!]\\centering\\begin{tabular}{|c|c|c|c|c|}\\hline $p$ & $f(x)$ & $\\edim\\, C_P$ & $\\dim_{k_P}T_P(C/\\Z)$ & $\\dim_{k_P}T_P(C/\\Z[\\xi])$ \\\\  \\hline\\hline" );
    
    for r in res do
        PrintFile( "file", r[1] );
        PrintFile( "file", "&" );
        PrintFile( "file", "$" );
        PrintFile( "file", r[2] );
        PrintFile( "file", "$" );
        PrintFile( "file", "&" );
        PrintFile( "file", r[3] ); 
        PrintFile( "file", "&" );
        PrintFile( "file", r[4] );
        PrintFile( "file", "&" );
        PrintFile( "file", r[5] );
        PrintFile( "file", "\\\\\\hline" );
    end for;
    
    PrintFile( "file", "\\end{tabular}\\caption{The singularities of $\\rbar{" cat GrpName cat "}$}\\label{tab:" cat GrpName cat "}\\end{table}");

        
    return res;
end function;
    
    
PrintGroups := function( grps, names )
    
    for i in [1..#grps]  do
        _ := ComputeGroup( grps[i] : ToFile := true, GrpName := 
                     names[i] );
    end for;
    
    return true;
end function;
    