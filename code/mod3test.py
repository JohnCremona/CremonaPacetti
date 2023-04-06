from sage.all import ZZ, QQ, GF, DirichletGroup, prime_pi, Primes, primes, Set, NumberField, Matrix, vector, polygen, prod, PolynomialRing

from read_modell_data import read_data, DATA_DIR
from mod2test import display_string, display_all, get_cubics
assert display_string # for pyflakes, since not used in this file
assert display_all    # for pyflakes, since not used in this file

from poly_utils import pol_simplify
from T0T1T2 import get_T1
from T0mod3 import get_T0_mod3, mod_p_fact_degs
from S4 import D4_extensions, S4_extensions, V4_extensions

try:
    assert len(quartic_lists)
except:
    quartic_lists = {}

def S4D4V4_extensions(S, D, cubics, verbose=True):
    # NB we know that D<0 so (a) nontrivial and (b) C4 impossible
    S4s = sum([S4_extensions(QQ,S, M=NumberField(cubic, 'm'), D=D, check_M=False, check_D=False)
               for cubic in cubics], [])
    # S4s = []
    # for cubic in cubics:
    #     S4sc = S4_extensions(QQ,S, M=NumberField(cubic, 'm'), D=D, check_M=False, check_D=False)
    #     S4sc = [pol_simplify(c, use_polredabs=True) for c in S4sc]
    #     S4s += S4sc
    #     if verbose:
    #         print(f"S={S}, D={D}, cubic={cubic}: {len(S4sc)} S4 quartics: {S4sc}")
    if verbose:
        print(f"S={S}, D={D}, cubics={cubics}: {len(S4s)} S4 quartics:")
        print(S4s)

    D4s = D4_extensions(QQ,S, d1=D, check_d1=False)
    assert all([f.discriminant().squarefree_part()==D for f in D4s])
    if verbose:
        print("S={}, D={}: {} D4 quartics".format(S,D,len(D4s)))
        print(D4s)

    # We want quartics defining V4s which have discriminant D (so they
    # will be reducible)
    V4s = V4_extensions(QQ,S, D=D, check_D=False)
    assert all([f.discriminant().squarefree_part()==D for f in V4s])
    if verbose:
        print("S={}, D={}: {} V4 quartics".format(S,D,len(V4s)))
        print([f.factor() for f in V4s])

    return S4s + D4s + V4s

def get_quartics(S, D, cubics):
    """Return from the cacahe or compute a list of S4,D4 or V4 quartics
    unramified outside S, with discriminant D and (for S4s) with cubic
    resolvent in the list cubics.
    """
    global quartic_lists
    SS = tuple(S)
    CC = tuple(cubics)
    if not (SS,D,CC) in quartic_lists:
        quartic_lists[(SS,D,CC)] = S4D4V4_extensions(S, D, cubics)
    return quartic_lists[(SS,D,CC)]

try:
    assert len(T1data)
except:
    T1data = {}

def get_T1data(S):
    global T1data
    SS = tuple(S)
    if not SS in T1data:
        T1data[SS] = get_T1(QQ,S)
    return T1data[SS]

try:
    assert len(T0mod3)
except:
    T0mod3 = {}

def get_T0mod3data(S, D, quartics):
    global T0mod3
    # print("In get_T0mod3data with S={}, D={}, and quartics={}".format(S,D,quartics))
    SSD = (tuple(S),D,tuple(quartics))
    if not SSD in T0mod3:
        # print("New (S,D)")
        _, T0, vlist = get_T0_mod3(QQ,S,quartics, verbose=False)
        # print("{} quartics, size of vlist = {}".format(len(quartics),len(vlist)))
        # print("caching")
        T0mod3[SSD] = [T0, vlist]
    else:
        # print("Repeat (S,D)")
        # print("{} quartics, size of cached vlist = {}".format(len(quartics),len(T0mod3[SSD][1])))
        pass
    return T0mod3[SSD]

def linear_lift(S, f, det_char, tr, verbose=True):
    r"""Given f, a quartic defining an S4, D4 or V4- extension unramified
    outside S with disc(f)=D, and functions det_char and tr from
    {primes not in S} to F^* and F=GF(3) respectively, which are a
    blackbox mod-3 representation whose projective kernel is cut out
    by f, return an octic which cuts out the linear representation.

    """
    D = f.discriminant()
    if verbose:
        print("-------------------------------------------------")
        print("In linear_lift with f = {}, D = {} ~ {}".format(f.factor(), D, D.squarefree_part()))
    V4 = not f.is_irreducible()
    F =  f.splitting_field('a') if V4 else NumberField(f, 'a')
    assert V4 or not F(D).is_square()
    SF = sum([F.primes_above(p) for p in S], [])
    V, alphas, fromV, toV = F.selmer_space(SF, ZZ(2))

    # if not V4:
    #     GG = {}
    #     for a in F.selmer_group_iterator(SF,2):
    #         ma = a.minpoly()
    #         x = polygen(QQ)
    #         g = pol_simplify(ma(x**2), use_polredabs=True)
    #         if g.degree()==8 and g.is_irreducible():
    #             G = g.galois_group('pari')
    #             Gname = str(G).split('"')[1]
    #             if Gname in GG:
    #                 GG[Gname] +=1
    #             else:
    #                 GG[Gname] = 1
    #             # if Gname == '2S_4(8)=GL(2,3)':
    #             an = a.norm()
    #             # if an.is_square() or (D*an).is_square():
    #             if G.order()==48:
    #                 print("alpha with norm {} (={} mod squares), coords {}, group={} (order {})".format(a.norm(), a.norm().squarefree_part(), toV(a),
    #                                                                                                     Gname,G.order()))
    #             # else:
    #             #     if a.norm().is_square():
    #             #         print("bad  alpha = {}, norm = {}, coords {}, group {} of order {}".format(a, a.norm().factor(), toV(a), Gname, G.order()))
    #             #         #print("g = {} has Galois group {}".format(g, Gname))
    #         else:
    #             print("alpha = {} with min poly {}".format(a, ma))
    #             print("g = {} has degree only {}".format(g, g.degree()))
    #     print("Groups with multiplicities: {}".format(GG))

    r = len(alphas)
    if verbose:
        print("{} alphas: {}".format(len(alphas),alphas))

    # Initialize T to be empty and A to be a matric with 0 rows and r=#alphas columns
    T = []
    A = Matrix(GF(2),0,r)
    rA = 0
    x = polygen(F)
    target_rank = r if V4 else r-1
    for p in Primes():
        if p in S or p.divides(D):
            continue
        if mod_p_fact_degs(f,p)==[1,1,2]:
            continue
        P = F.prime_above(p)
        if any([a.valuation(P)!=0 for a in alphas]):
            continue
        FP = P.residue_field()
        v = vector([1-FP(a).is_square() for a in alphas])
        A1 = A.stack(v)
        rA1 = A1.rank()
        if rA1 > rA:
            A = A1
            rA = rA1
            T.append(p)
        if rA == target_rank:
            break
    assert A*vector(toV(F(D))) == 0
    if verbose:
        print("Test set of primes: {}".format(T))
        #print("A-matrix =\n{}".format(A))
    if verbose:
        F3t = PolynomialRing(GF(3), 't')
        print("Frobenius polys: {}".format([F3t([det_char(p), -tr(p), 1]) for p in T]))
    b = [1 - ( (tr(p), det_char(p)) in [(0,2), (2,1)] ) for p in T]
    if verbose:
        print("Test vector: {}".format(b))
    
    e = list(A.solve_right(vector(b)))
    assert A*vector(e) == vector(b)
    if verbose:
        print("exponent vector: {}".format(e))
    alpha = fromV(e)
    ma = alpha.minpoly()
    if verbose:
        print("alpha = {} with min poly {}".format(alpha, ma))
        print("  coords {}".format(toV(alpha)))
    if V4:
        M = F.extension(x**2-alpha, 'b').absolute_field('c')
        G = M.galois_group()
        G_label = G.pari_label()
        if verbose:
            print("V4 case. M={} with Galois group {}".format(M, G_label))
        LL = [L for L,i,j in M.subfields() if L.degree()==4 and not L.is_galois()]
        assert len(LL)==4
        # This contains two isomorphic copies of each of the sibling quartics
        # So we pick one with each discriminant (which must be different)
        DL = Set([L.disc() for L in LL])
        g = prod([next(pol_simplify(L.defining_polynomial(), use_polredabs=True) for L in LL if L.disc()==d) for d in DL])
    else:
        x = polygen(QQ)
        g = pol_simplify(ma(x**2), use_polredabs=True)
        assert g.degree()==8 and g.is_irreducible()
        G = g.galois_group(pari_group=True)
        G_label = G.label()
    if verbose:
        print("linear_lift returns octic {} with group {}".format(g, G_label))
        print("-------------------------------------------------")
    return g

# Process a single form data packet:

def get_disc(data):
    G = DirichletGroup(data['N'], GF(3))
    # Select the char mod 3 whose values match the data:
    chi = next(g for g in G if all([g(a)==b for a,b in data['chi_list']]))
    data['chi'] = chi
    F3 = GF(3)
    k = data['k']
    det_char = lambda p: F3(p)**(k-1) * chi(p)
    data['det_char'] = det_char
    T1, A, decoder = get_T1data(data['S'])
    data['disc'] = D = decoder([0 if det_char(p)==1 else 1 for p in T1])
    return D

def get_possible_cubics(data, verbose=True):
    r"""Given data with discriminant already computed, return a list of possible resolvent cubics.

    Starting with all cubics with discriminant D, we can eliminate
    those which are irreducible modulo any prime with
    char.poly. x^2+1.  Such primes exist if and only if the
    representation is irreducible.  In this case we expect there to be
    enough data to eliminate all but one cubic, but we do not rely on
    this.  The fewer cubics we have after this stage, the fewer
    quartic lists we will have to compute and test later.

    Returns (boolean,list). The boolean is True iff we have
    established irreducibility; when False we expect reducibility but
    have not proved it.  The list is a (possibly empty) list of
    possible cubic resolvent polynomials.  These will be used to
    restrict the possible S4 extensions considered next.

    """
    S = data['S']
    D = data['disc']
    tr = data['tr']
    det3 = data['det_char']

    cubics = get_cubics(S, D)
    ncubics = len(cubics)
    if verbose:
        print(f"{ncubics} cubics have discriminant {D} modulo squares: {cubics}")

    # Find "irreducibility witness primes" with char poly x^2+1:
    useful_primes = [p for p in primes_first_n(data['nap']) if p not in S and det3(p)==+1 and tr(p)==0]
    irred = len(useful_primes)>0
    if not irred:
        if verbose:
            print("Probably reducible: no irreducibility witness primes")
        return False, cubics

    print(f"Irreducible: {len(useful_primes)} witness primes: {useful_primes}")

    test = lambda cub,p: mod_p_fact_degs(cub,p) == [1,1,1] or p.divides(cub.discriminant())
    # for cub in cubics:
    #     print(f"Testing cubic {cub}")
    #     for p in useful_primes:
    #         print(f" mod {p} factors as {mod_p_fact_degs(cub,p)}")
    cubics = [cub for cub in cubics if all(test(cub,p) for p in useful_primes)]
    ncubics = len(cubics)
    print(f"After testing for irreducibility modulo all witness primes, {ncubics} remain: {cubics}")
    return True, cubics

def check1form(data, verbose=False):
    assert data['ell'] == 3
    F3 = GF(3)
    label = data['label']
    if verbose:
        print("==========================================================")
        print("label = {}".format(label))
    N = data['N']
    S = data['S']
    k = data['k']
    d = data['d']
    ap = data['ap']

    if verbose:
        print("N = {}".format(N))
        print("k = {}".format(k))
        print("d = {}".format(d))
        print("S = {}".format(S))

    data['tr'] = tr = lambda p: F3(ap[prime_pi(p)-1])
    data['atr'] = atr = lambda p: int(tr(p)!=0)

    # Step 1: compute the determinant character

    D = get_disc(data) # sets data['disc']
    if verbose:
        print(f"character = {data['chi']}")
        print(f"discriminant = {D}" + (" (cyclotomic)" if D==-3 else ""))
        det_char = data['det_char']

    # Since these are odd representations, the discriminant will
    # always be negative, and in particular not 1:
    assert D<0
    
    # Step 2: compute the cubic resolvent:

    irred, cubics = get_possible_cubics(data, verbose)
    # NB irred==True means certainly irreducible (we found primes
    # with char.poly. x^2+1) but irred==False only means we found no
    # such prime, so the representation is probably reducible but we
    # will establish that rigorously.
    if verbose:
        if irred:
            print(f"Irreducible, possible cubic resolvents {cubics}")
        else:
            print(f"Probably reducible, possible cubic resolvents {cubics}")

    if not irred:
        print("{} mod {}: Reducible".format(label, 3))
        data['reducible'] = True
        return data

    # Step 3: find all possible quartics
    
    quartics = get_quartics(S, D, cubics)
    if verbose:
        print("{} candidate quartics".format(len(quartics)))

    # Step 4: test irreducibility, cutting down the possible quartics
    # (possibly to none).

    # quartics2 = []
    # for f in quartics:
    #     p =  next(p for p in Primes() if (not p in S) and mod_p_fact_degs(f,p)==[2,2])
    #     if det_char(p)==1 and tr(p)==0:
    #         quartics2.append(f)
    #         if verbose and not irred:
    #             print("Irreducible via p={}".format(p))
    #         irred = True
    # quartics = quartics2

    # # If all quartics have been eliminated, the representation is reducible:
    
    # if not irred:
    #     print("{} mod {}: Reducible".format(label, 3))
    #     data['reducible'] = True
    #     return data

    # Step 4: eliminate quartics by matching
    # factorization patterns to Frobenius polynomials:
    #
    # [4]:                |ap|=1, chi=-1
    # [1,3] or [1,1,1,1]: |ap|=1, chi=+1
    # [1,1,2]:            ap=0,   chi=-1
    # [2,2]:              ap=0,   chi=+1

    fact_pats = {(1, 2): [[4]],
                 (1, 1): [[1,3],[1,1,1,1]],
                 (0, 2): [[1,1,2]],
                 (0, 1): [[2,2]]}
    poss_fact_pat = lambda p: fact_pats[(atr(p), det_char(p))]
    test = lambda f,p: mod_p_fact_degs(f,p) in poss_fact_pat(p)
    
    Sx = Set(sum([f.discriminant().support() for f in quartics], S))
    test_primes = [p for p in primes(data['maxp']) if p not in Sx]
    quartics = [f for f in quartics if all(test(f,p) for p in test_primes)]

    if verbose:
        print("After testing all p<{}, {} possible quartics remain".format(data['maxp'],len(quartics)))
        
    if not quartics:
        # If we get here, we must have a reducible representation
        if irred:
            data['pol'] = None
            data['gal'] = None
            data['reducible'] = None
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print(" label = {} has a problem: reducibility not established but no quartic matches".format(label))
            #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            raise RuntimeError
        print("{} mod {}: Reducible".format(label, 3))
        data['reducible'] = True
        return data
      
    
    # Otherwise, if just one quartic remains, the representation is
    # irreducible with this kernel polynomial:
    
    if len(quartics)==1:
        pol = quartics[0]
        if pol.is_irreducible():
            pol = pol_simplify(pol, use_polredabs=True)
            id = pol.galois_group().id()
            data['gal'] = gal = 'S4' if id==[24,12] else 'D4'
        else:
            data['gal'] = gal = 'V4'
        data['pol'] = pol
        
        if verbose:
            print("Irreducible: projective splitting field polynomial = {} with group {}".format(pol,gal))
        data['reducible'] = False
        data['octic'] = octic = linear_lift(S, pol, det_char, tr, verbose=verbose)
        longGnames = ["2S_4(8)=GL(2,3)", "D_8(8)=[4]2", "2D_8(8)=[D(4)]2"]
        shortGnames = ["GL(2,3)", "Ns", "Nn"]
        M = octic.splitting_field('c') if gal=='V4' else NumberField(octic, 'c')
        G = M.galois_group()
        Gorder = 48 if gal=='S4' else 16 if gal=='D4' else 8
        G_label = G.pari_label()
        if G.order() != Gorder:
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print("! octic g = {} has Galois group of order {}, but should be {}   !".format(octic, G.order(), Gorder))
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            data['lingal'] = "?"
            raise RuntimeError
        else:
            data['lingal'] = Gname = shortGnames[longGnames.index(G_label)]
            assert [gal, Gname] in [['S4','GL(2,3)'], ['D4', 'Nn'], ['V4', 'Ns']]
        print(display_string(data,3))
        if verbose:          
            print("----------------------------------------------------------")
        return data
        
    # Step 5: Otherwise we find additional distinguishing primes.
        
    if verbose:
        print("##########################################################")
        print("Irreducible, polynomial is one of {}:  {}".format(len(quartics),quartics))
        print("Computing distinguishing test prime set T0")
        print("##########################################################")
    T0, vlist = get_T0mod3data(S,D,quartics)
    if verbose:
        print("test prime set T0: {}".format(T0))
        print("vlist = ")
        for v,q in zip(vlist,quartics):
            print("v={} for quartic {}".format(v,q))
            
    # Compute test vector.  Here ap=+1,-1 map to 1 and 0 to 0
    v = [int(tr(p0)!=0) for p0 in T0]
    if verbose:
        print("test vector = {}".format(v))
        
    # NB the vectors in vlist are distinct by construction, and v should equal exactly one of them:
    if v in vlist:
        i = vlist.index(v)
        pol = quartics[i]
        if pol.is_irreducible():
            pol = pol_simplify(pol, use_polredabs=True)
            id = pol.galois_group().id()
            data['gal'] = gal = 'S4' if id==[24,12] else 'D4'
        else:
            data['gal'] = gal = 'V4'
        data['pol'] = pol
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
        data['reducible'] = False
        data['octic'] = octic = linear_lift(S, pol, det_char, tr, verbose=False)
        longGnames = ["2S_4(8)=GL(2,3)", "D_8(8)=[4]2", "2D_8(8)=[D(4)]2"]
        shortGnames = ["GL(2,3)", "Ns", "Nn"]
        M = octic.splitting_field('c') if gal=='V4' else NumberField(octic, 'c')
        G = M.galois_group()
        G_label = G.pari_label()
        data['lingal'] = Gname = shortGnames[longGnames.index(G_label)]
        assert [gal, Gname] in [['S4','GL(2,3)'], ['D4', 'Nn'], ['V4', 'Ns']]
        print(display_string(data,3))
        if verbose:
            print("----------------------------------------------------------")
        return data
    else:
        # If we get here, we must have a reducible representation
        if irred:
            data['pol'] = None
            data['gal'] = None
            data['reducible'] = None
            print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            print(" label = {} has a problem: reducibility not established but no quartic matches".format(label))
            #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
            raise RuntimeError
        print("{} mod {}: Reducible".format(label, 3))
        data['reducible'] = True
        return data

def run(fname, dir=DATA_DIR, no_repeats=False, minN = None,  maxN = None, outfilename=None, verbose=False):
    ell = 3
    alldata = read_data(fname, ell, dir=dir)
    print(f"finished reading data: {len(alldata)} forms mod 3")
    if no_repeats:
        alldata = [data for data in alldata if data['i']==1]
        print(f" -- only processing {len(alldata)} distinct forms")
    if minN or maxN:
        if minN:
            alldata = [data for data in alldata if data['N']>=minN]
        if maxN:
            alldata = [data for data in alldata if data['N']<=maxN]
        print(f" -- only processing {len(alldata)} forms with level between {minN} and {maxN}")
    nreds = 0   # count of reducibles
    nirreds = 0 # count of irreducibles
    gal_counts = {'S4':0, 'D4':0, 'V4':0}   # counts of irreducibles with projective image S4, D4, V4
    gal_strings = {'S4': ' and surjective (projective splitting field S4)',
                   'D4': ' with image Nn, the normaliser of a Nonsplit Cartan (projective splitting field D4)',
                   'V4': ' with image Ns, the normaliser of a Split Cartan (projective splitting field V4'}

    if outfilename:
        with open(outfilename, 'a') as outfile:
            for data in alldata:
                res1 = check1form(data, verbose=verbose)
                outfile.write(display_string(res1, ell)+"\n")

                if res1['reducible']:
                    nreds += 1
                else:
                    nirreds += 1
                    gal_counts[res1['gal']] +=1
    else:
        for data in alldata:
            res1 = check1form(data, verbose=verbose)

            if res1['reducible']:
                nreds += 1
            else:
                nirreds += 1
                gal_counts[res1['gal']] +=1

    print("{} lines written to {}".format(nreds+2*nirreds, outfilename))
    print()
    print("{} forms are reducible and {} are irreducible".format(nreds,nirreds))
    for gal in gal_counts:
        print("{} forms are irreducible{}".format(gal_counts[gal], gal_strings[gal]))
