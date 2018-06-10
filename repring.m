/* Suppose that G is a finite group and Z[xi] is the extension of Z
   by a primitive |G|-th root of unity. The Green ring R(G) over Z[xi] 
   of G is the tensor product of R_0(G) with Z[xi] where R_0(G) is the 
   representation ring of G over Z.
  
   This file contains functions to compute prime ideals of R(G) and 
   check if they are singular. */
           
Attach( "primdecz/primdecz.magma" );            
            
// we extend the record fields of RngMPol in order to store some calculations


/* the following record fields will be appended to ideais I such that 
   Z[x_1,...,x_n]/I will be isomorphic to R(G). */


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

    
/* Check if the order of a multiplicative element is n. */

IsOrderOfFieldElement := function( x, n )
    
    if x^n ne 1 then
        return false;
    end if;
        
    primes := PrimeDivisors( n );
    for i in primes do
        if x^Round(n/i) eq 1 then
            return false;
        end if;
    end for;
    
    return true;
end function;
    
/* I is an ideal maximal in R=Z[x_1,...,x_k]. The function identifies
   the field R/I. Returns the field the the projection of R onto the field. */
    
ResidualField := function( I )
    
    /* if the field was computed already, we return it */
    
    if assigned I`residualField then
        return I`residualField, 
               I`projectionToResidualField, I`projectionToQuotient;
    end if;       
    
    // set up the polynomial ring first
    P := Parent( I.1 );
    
    // take the quotient and the natural projection
    Q, g := P/I;
    
    // Q is a field, but Magma does not identify it as such. 
    // first extract the characteristic
    p := Characteristic( Q );
    
    // rank is the number of variables
    rank := Rank( P );
    
    // P1 and I1 are copies of P and I over characteristic p
    P1 := PolynomialRing( GF( p ), rank );
    I1 := Ideal( [ P1!x : x in Basis( I ) ] );
    
    // F0 is the field P1/I1
    F0 := P1/I1;
    assert IsField( F0 );
    
    // we calculate the order of F0 and the dimension
    oF0 := #F0;
    dimF0 := Round( Log( p, oF0 ));
    
    // now we construct a linear generating set for F0 and Q in parallel
    
    gensF0 := []; gensQ := []; gensP := [];
    for i in [1..rank] do
        for j in [1..dimF0] do
            gensF0 := gensF0 cat [ F0.i^j  ];
            gensQ := gensQ cat [ Q.i^j ];
        end for;
    end for;
        
    // find a primitive element in the field by taking random 
    // linear combinations in the generating set
      
    repeat 
        vec := [ Random( GF( p )) : x in [1..#gensF0]];
        el := &+[ vec[i]*gensF0[i] : i in [1..#gensF0]];
        
    until IsOrderOfFieldElement( el, #F0-1 );
                              
    // now calculate a "nice" copy of F0                   
    mpol := MinimalPolynomial( el );
    F := SplittingField( mpol );
    
    // elQ is the element of Q that corresponds to el in F0
    elQ := &+[ (Integers()!vec[i])*gensQ[i] : i in [1..#gensQ]];
                   
    // we can list the elements of Q                   
    listQ := [ Q!0 ] cat [ elQ^i : i in [0..#F-2]];
                   
    // fun is a function that will define a bijection from P -> F               
    fun := function( x )
        
        if x eq Zero( Q ) then 
            return Zero( F );
        else
            pos := Position( listQ, x );
            assert pos ge 2;
            return PrimitiveElement( F )^(pos-2);
        end if;
        
    end function;
        
    // set up the bijective map Q -> F    
    mapQF := pmap< Q -> F | x:->fun(x) >;
    I`residualField := F;
    I`projectionToQuotient := g;
    I`projectionToResidualField := mapQF;
        
    return F, g, mapQF;
end function;
    
    
/* The next funcion defines the ring R(G) tensor Z[xi] where 
    xi is |G|-th root of unity in C. */
    
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
    for i in [1..#B] do
        for j in [1..deg] do
            Append( ~J, Derivative( B[i], j ));
        end for;
    end for;
    
    J := Matrix( #B, deg, J );
                 
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
    
/* for some reason, exponentiation is slow in the ring constructed in 
   GreenRingAsFiniteDimensionalAlgebra. The next function replaces 
   exponentiation with product. 
  
   computes el^n, one is the identity of the ring */
  
MyExp := function( el, n, one )  
    
    if n eq 0 then 
        return one; 
    else
        return &*[ el : i in [1..n]];
    end if;
    
end function;
    
/* if el is the element of a polynomial ring in one variables, calculates
   the list of coefficients. */
    
ListCoeffs := function( el, deg, X )
    
    list := Coefficients( el, X );
    list := list cat [ 0 : i in [1..deg-#list]]; // extend to the right length
                    
    return list;
end function;

// We construct the Green ring of a group G as a Z-module of finite rank

GreenRingAsFiniteDimensionalAlgebra := function( I )
    
    // check if this is constructed already
    
    if assigned I`greenRingAsFiniteDimensionalAlgebra then
        return I`greenRingAsFiniteDimensionalAlgebra,
               I`embeddingsOfGreenRingAsFiniteDimensionalAlgebra[1],
               I`embeddingsOfGreenRingAsFiniteDimensionalAlgebra[2];    
    end if; 
        
    // set up variables
    G := I`greenRingOfGroup;
    deg_cyc := Degree( I`cyclotomicPolynomial );
    P := I`polynomialRing;
    R := I`coefficientRingOfGreenRing;
    X := R.1;
    irr := CharacterTable( G );
    deg := #irr;     
      
    // set up the initial multiplication table for A with zeros
      
    table := [ [ [0 : z in [1..deg] ] : y in [1..deg]] : x in [1..deg]];
    
    // calculate products in A by decomposing the characters xi*xj
    
    for i in [1..deg] do
        for j in [i..deg] do
            dec := Decomposition( irr, irr[i]*irr[j] );
            for d in [1..#irr] do
                table[i][j][d] := dec[d];
                table[j][i][d] := dec[d];
            end for;
        end for;
    end for;
    
    // define the R-algebra A using the mult table
      
    A := Algebra< R, deg | table >;
    
    /* we will set up a homorphism from the polynomial ring to 
       A with kernel equal to the ideal constructed in 
       IdealOfRepresentation ring */
      
    // compute the matching sequence of generators   
    gensA := [ A.i : i in [2..#irr]] cat [X*A.1];
    gensP := [ One( P ) ] cat [ P.i : i in [1..#irr]];
                     
    // the function that maps an element of P to A                 
                     
    __func_P2A := function( f )
        co, mo := CoefficientsAndMonomials( f );
        el_a := Zero( A );
        for i in [1..#co] do
            exp := Exponents( mo[i] );
            mon := &*[ MyExp( gensA[i], exp[i], A.1 ) : i in [1..#exp]];
                           el_a := el_a+co[i]*mon;
        end for;
        return el_a;
    end function;
        
    // the function that maps an element of A into P    
        
    __func_A2P := function( a )
        
        xx := P.(#irr);
        
        el := Zero( P );
        
        for i in [1..#irr] do
            coeffs := ListCoeffs( a[i], deg_cyc, X );
            co := &+[ xx^(j-1)*coeffs[j] : j in [1..#coeffs]];
            el := el + co*gensP[i];
        end for;
        
        return el;
    end function;
        
    // finish off    
        
    map_p2a := map< P -> A | x :-> __func_P2A( x )>;
    map_a2p := map< A -> P | a :-> __func_A2P( a )>;        
    
    I`greenRingAsFiniteDimensionalAlgebra := A;
    I`embeddingsOfGreenRingAsFiniteDimensionalAlgebra := < map_p2a, map_a2p >;
    
    return A, map_p2a, map_a2p;
end function;
        
/* the following function calculates the order of K/K^2 for a prime ideal
   K in the Green ring R(G). */
    
ImageOfPOverP2InGreenRing := function( K )
    
    // set up variables
    I := K`idealOfGreenRing;
    P := I`polynomialRing;
    GR, map_P2GR, map_GR2P := GreenRingAsFiniteDimensionalAlgebra( I );
    G := I`greenRingOfGroup;
    no_irrs := #CharacterTable( G );
    deg_cyc := Degree( CyclotomicPolynomial( #G ));
    R := CoefficientRing( GR );                     
    X := R.1;
    
    /* the generators of ht GR that correspond to non-trivial characters 
       the root of unity xi. */
      
    gensGR := [ GR.i : i in [2..no_irrs]] cat [X*GR.1];
    
    Gr := GroebnerBasis( K ); Gr2 := GroebnerBasis( K^2 );
    
    // map the elements of Gr into GR
    
    els_a := [ f@map_P2GR : f in Gr ];
    
    length := #els_a;
      
    // calculate a Z-basis for GR  
    zbas := [ GR.i*X^j*GR.1 : i in [1..Dimension( GR )], j in [0..deg_cyc-1]];
    
    /* multiply all elements of els_a with the elements of the Z-basis
       the make sure we get a Z-generating set for the image of K. */
    
    for e in [1..length] do
        for b in zbas do
            Append( ~els_a, els_a[e]*b );
        end for;
    end for;
    
    // do the same with K^2
    
    els_a2 := [ f@map_P2GR : f in Gr2 ];
    
    length := #els_a2;
    
    for e in [1..length] do
        for b in zbas do
            Append( ~els_a2, els_a2[e]*b );
        end for;
    end for;
    
    // set up the module Z^n
    
    Zn := RModule( Integers(), deg_cyc*no_irrs );
    
    // calculate the Z-generators of the image of K inside Zn
    gens := [];
        
    for el in els_a do
        zgen := &cat[ ListCoeffs( i, deg_cyc, X ) : i in Eltseq( el )];
        Append( ~gens, zgen );
    end for;
    
    // calculate the Z-generators of the image of K^2 inside Zn
    gens2 := [];
    
    for el in els_a2 do
        zgen := &cat[ ListCoeffs( i, deg_cyc, X ) : i in Eltseq( el )];
        Append( ~gens2, zgen );
    end for;
    
    // set up the Z-matrices with the Z-generators of K and K^2
    mat := Matrix( Integers(), #gens, no_irrs*deg_cyc, gens );
    mat2 := Matrix( Integers(), #gens2, no_irrs*deg_cyc, gens2 );
                           
    // The orders of P/K and P/K^are given by the elementary divisors
                    
    return ElementaryDivisors( mat ), ElementaryDivisors( mat2 );
end function;
    
/* calculate the embedding dimension of a prime ideal K. This equal
   to the k_K-dimension of the localization of (K/K^2)_(K). In this 
  case the localization is isomorphic to K/K^2. */
  
EmbeddingDimension := function( K )
    
    // if computed already then return it.
                                       
    if assigned K`embeddingDimension then
        return K`embeddingDimension;
    end if; 
    
    // calculate the elementary divisors that correspond to K and K^2
    
    I := K`idealOfGreenRing;
    GR := GreenRingAsFiniteDimensionalAlgebra( I );
    eldiv, eldiv2 := ImageOfPOverP2InGreenRing( K );
    
    // calculate the dimension
    
    emdiv := Round( Log( &*eldiv, &*eldiv2/&*eldiv ));
    assert (&*eldiv)^emdiv eq &*eldiv2/&*eldiv;
    
    K`embeddingDimension := emdiv;
    return emdiv;
end function; 
    
// subsbstitute the elements into the residual field    
    
JacobianOverResidualField := function( K )
    
    if assigned K`jacobian then
        return K`jacobian;
    end if; 
    
    F, g, mpf := ResidualField( K );
    I := K`idealOfGreenRing;
    P := I`polynomialRing;
    B := GroebnerBasis( I );
    J := I`generalJacobian;
    Jp := Matrix( F, #B, Rank( P ), [ x@g@mpf : x in Eltseq( J )] );
    K`jacobian := Jp;
    
    return Jp;
end function;
    
DimensionOfZariskiTangentSpace := function( K )
    
    return Dimension( Nullspace( Transpose( JacobianOverResidualField( K ))));
end function;    
    
/* Compute the minimal primes in the Green ring R(G).
   The minimal primes correspond to class functions chi such that ch(c)=0
   on a fixed class c. 
  
   The next function computes the minimal prime that vanishes on the k-th
   conjugacy class. */
  
MinimalPrimeIdealOfGreenRing := function( I, k )
    
    G := I`greenRingOfGroup;
    T := CharacterTable( G );
    F := Universe( &cat[ Eltseq( x ) : x in T ] );
    P := I`polynomialRing;
    // the k-th column of the table
      
    col := [ irr[k] : irr in T];
    first := 1;
    
    gens := [];
    
    for i in [1..#col] do
        if i ne first then    
           gen := [ Zero( F ) : x in [1..#col]];
           gen[first] := -col[i];
           gen[i] := 1;
           gens := gens cat gen;
       end if;
   end for;
   
   mat := Matrix( F, #T-1, #T, gens );
           
   gensM := [];
   gensP := [ One( P )] cat [ P.i : i in [1..#T-1]];
                    
   degF := Degree( F );
   XX := P.(#T)^Round(#G/degF); 
            
   for i in [1..#T-1] do
       Append( ~gensM, &+[ &+[Round( Eltseq( mat[i][j] )[u+1])*XX^u : 
               u in [0..degF-1]]*gensP[j] : j in [1..#T]]);
   end for;

   return Ideal( gensM );    
end function;
  
// compute the prime ideals of the Green ring over a prime p
  
PrimeIdealsOfGreenRingWithPrime := function( I, p )
    
    B := GroebnerBasis( I );
    // attach p to the ideal
    Bp := Append( B, p );
    Ip := Ideal( Bp );
    
    P := I`polynomialRing;

    
    _, dec := PrimaryDecompositionZ( Ip );
    
    listideals := [];
    for K in dec do 
        KK := K;
        KK`prime := p;
        KK`idealOfGreenRing := I;
        Append( ~listideals, KK );
    end for;
    
    return listideals;
end function;