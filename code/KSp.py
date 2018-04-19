# JEC's K(S,p) code originally written in Magma
#

from sage.all import prod, Matrix, GF, VectorSpace, QQ

def IdealGenerator(I):
    try:
        return I.gens_reduced()[0]
    except AttributeError:
        return I

# fractional ideals have no support method, but field elements do

def Support(a):
    try:
        return a.support()
    except AttributeError:
        return a.prime_factors()

def coords_in_C_p(I,C,p):
    """For an ideal I of a field with class group C, such that I^p is
    principal, return the coordinates of [I] in C[p].
    """
    #print("I = {}".format(I))
    c = C(I).exponents()
    #print("c = {}".format(c))
    #print("structure = {}".format(C.gens_orders()))
    non_p_indices = [i for i,n in enumerate(C.gens_orders()) if not p.divides(n)]
    #print("non_p_indices = {}".format(non_p_indices))
    assert all([c[i]==0 for i in non_p_indices])
    p_indices = [(i,n//p) for i,n in enumerate(C.gens_orders()) if p.divides(n)]
    #print("p_indices = {}".format(p_indices))
    assert all([c[i]%n==0 for i,n in p_indices])
    return [(c[i]//n)%p for i,n in p_indices]

def coords_in_C_mod_p(I,C,p):
    """For an ideal I of a field with class group C, return the coordinates of [I] in C/C^p.
    """
    c = C(I).exponents()
    p_indices = [i for i,n in enumerate(C.gens_orders()) if p.divides(n)]
    return [c[i]%p for i in p_indices]

def root_ideal(I,C,p):
    """Given an ideal I whose class is a p'th power in the class group C,
    return an ideal J such that I is equivalent to J^p.
    """
    v = C(I).exponents()
    # In the line below, e=(vi/p)%n should satisfy p*e=vi (mod n)
    w = [vi//p if p.divides(n) else (vi/p)%n for vi,n in zip(v,C.gens_orders())]
    return prod([J**wi for wi,J in zip(w,C.gens_ideals())], C.number_field().ideal(1))

def coords_in_U_mod_p(u,U,p):
    """For a unit u in a field with unit group U, return the coordinates of u in U/U^p
    """
    co = U.log(u)
    if not p.divides(U.zeta_order()):
        co = co[1:]
    return  [c%p for c in co]

def basis_for_p_cokernel(S,C,p):
    """Return a basis for the group of ideals supported on S (mod
    p-powers) whose class in the class group C is a p'th power,
    together with a function which takes the S-exponents of such an
    ideal and returns its coordinates on this basis.
    """
    M = Matrix(GF(p),[coords_in_C_mod_p(P,C,p) for P in S])
    k = M.left_kernel()
    bas = [prod([P**bj.lift() for P,bj in zip(S,b.list())], C.number_field().ideal(1)) for b in k.basis()]
    f = lambda v: k.coordinate_vector(v)
    return bas,f

# The function itself

def pSelmerGroup(K, S, p, debug=False):

    #Computes the p-S-Selmer group of the number field containing the ideals in S

    if not all(P.is_prime() for P in S):
        raise ValueError("elements of S must all be prime")
    if not p.is_prime():
        raise ValueError("p must be prime")

    F = GF(p)

    # Step 1. The unit contribution: all fundamental units, and also the
    # generating root of unity if its order is a multiple of p; we just
    # take generators of U/U^p.  These have valuation 0 everywhere.

    hK = K.class_number()
    C = K.class_group()
    hKp = (hK%p == 0)

    if K == QQ:
        if p == 2:
            ulist = [QQ(-1)]
        else:
            ulist = []
    else:
        U = K.unit_group()
        ulist = U.gens_values()
        if U.zeta_order()%p:
            ulist = ulist[1:]
    if debug: print("{} generators in ulist = {}".format(len(ulist),ulist))

    # Step 2. The class group contribution: generators of the p'th
    # powers of ideals generating the p-torsion in the class group.
    # These have valuation divisible by p everywhere.

    if hKp:
        betalist = [IdealGenerator(c**n) for c,n in zip(C.gens_ideals(), C.gens_orders()) if n%p==0]
    else:
        betalist = []
    if debug: print("{} generators in betalist = {}".format(len(betalist),betalist))

    # Step 3. The part depending on S: one generator for each ideal A
    # in a basis of those ideals supported on S (modulo p'th powers of
    # ideals) which is a p'th power in the class group.  We find B
    # such that A/B^p is principal and take a generator of that, for
    # each A in a generating set.

    if hK > 1:
        T, f = basis_for_p_cokernel(S,C,p)
        alphalist = [IdealGenerator(I/root_ideal(I,C,p)**p) for I in T]
    else:
        f = lambda x:x
        alphalist = [IdealGenerator(P) for P in S]

    if debug: print("{} generators in alphalist = {}".format(len(alphalist), alphalist))

    # Now we have the generators of K(S,p), and define K(S,p) as an
    # abstract vector space:

    KSp_gens = alphalist + betalist + ulist
    if debug: print("Generators of K(S,p) = {} (dimension {})".format(KSp_gens, len(KSp_gens)))
    KSp = VectorSpace(GF(p), len(KSp_gens))

    # Now we define maps in each direction from the abstract space and K^*.

    # Define the easy map from KSp into K^*:

    def from_KSp(v):
        return prod([g**vi for g,vi in zip(KSp_gens,v)], K(1))

    # Define the hard map from (a subgroup of) K^* to KSp:

    def to_KSp(a):
        # Check that a is in K(S,p):
        assert a != 0
        assert all(P in S or a.valuation(P)%p==0 for P in a.support())

        # 1. (a) is a p'th power mod ideals in S, say (a)=AB^p, where
        # A is supported on S and is a linear combination of the
        # ideals T above.  Find the exponents of the P_i in S in A:

        S_vals = [F(a.valuation(P)) for P in S]
        avec = list(f(S_vals)) # coordinates of A w.r.t ideals in T (mod p'th powers)
        a1 = prod((alpha**e for alpha,e in zip(alphalist,avec)), K(1))
        a /= a1
        if debug: print("alpha component is {} with coords {}".format(a1,avec))
        if debug: print("continuing with quotient {} whose ideal should be a {}'th power: {}".format(a,p,K.ideal(a).factor()))

        # 2. Now (a) is a p'th power, say (a)=B^p.
        # Find B and the exponents of [B] w.r.t. basis of C[p]:

        supp = a.support()
        vals = [a.valuation(P) for P in supp]
        assert all(v%p==0 for v in vals)
        B = prod((P**(v//p) for P,v in zip(supp,vals)),K.ideal(1))
        assert B**p == K.ideal(a)

        if hKp:
            bvec = coords_in_C_p(B,C,p)
            a2 = prod((beta**e for beta,e in zip(betalist,bvec)), K(1))
            a /= a2
            supp = a.support()
            vals = [a.valuation(P) for P in supp]
            assert all(v%p==0 for v in vals)
            B = prod((P**(v//p) for P,v in zip(supp,vals)),K.ideal(1))
            assert B**p == K.ideal(a)
        else:
            bvec = []
            a2 = 1

        if debug: print("beta component is {} with coords {}".format(a2,bvec))
        if debug: print("continuing with quotient {} which should be a p'th power times a unit".format(a))

        # 3. Now (a) = (c)^p for some c, so a/c^p is a unit

        assert B.is_principal()
        a3 = IdealGenerator(B)
        a /= a3**p
        if debug: print("dividing by {}th power of {}".format(p,a3))
        if debug: print("continuing with quotient {} which should be a unit".format(a))

        #4. Now a is a unit

        # NB not a.is_unit which is true for all a in K^*.  One could
        # also test K.ring_of_integers()(a).is_unit().
        assert K.ideal(a).is_one()

        if K == QQ:
            if p == 2:
                cvec = [1] if a == -1 else [0]
            else:
                cvec = []
        else:
            cvec = coords_in_U_mod_p(a,U,p)
        if debug: print("gamma component has coords {}".format(cvec))

        return KSp(avec + bvec + cvec);

    return KSp, KSp_gens, from_KSp, to_KSp


"""

Notes on computing the map:

Given a in KSp:
(1) Write (a) in the form AB^p with A supported by S and p'th power free;

Set IS = group of ideals spanned by S mod pth powers, and ISP=subgroup
of that which map 0 in Cl/Cl^p

(2) Convert A to an element of ISP, hence find the component w.r.t. alphalist 
of a;  

(3) Dividing out by that, now (a)=B^p (with a different B).  

Write [B] in terms of the generators of Cl[p], then B=B1*(b) 
where the coefficients of B1 w.r.t. Cl[p]-gens give the component of 
result w.r.t. betalist. 

(4) Dividing out by that, and by b^p, we have (a)=(1), so a is a unit.

Now a can be expressed in terms of the unit generators:  
fundamental units first then (if necessary) root of unity.

"""

