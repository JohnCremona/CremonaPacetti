from sage.all import ZZ, QQ, GF, DirichletGroup, prime_pi, Primes, primes, Set, NumberField, Matrix, vector, polygen, prod, PolynomialRing

from read_modell_data import read_data, DATA_DIR
from mod2test import display_string, display_all
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

def S4D4V4_extensions(S, D, verbose=False):
    # NB we know that D<0 so (a) nontrivial and (b) C4 impossible
    S4s = S4_extensions(QQ,S, D=D, check_D=False)
    assert all([f.discriminant().squarefree_part()==D for f in S4s])
    if verbose:
        print("S={}, D={}: {} S4 quartics".format(S,D,len(S4s)))
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

def get_quartics(S, D=None):
    global quartic_lists
    SS = tuple(S)
    if not (SS,D) in quartic_lists:
        quartic_lists[(SS,D)] = S4D4V4_extensions(S, D)
    return quartic_lists[(SS,D)]

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

def check1form(data, verbose=False):
    assert data['ell'] == 3
    F3 = GF(3)
    label = data['label']
    if verbose:
        print("==========================================================")
        print("label = {}".format(label))
    N = data['N']
    S = (3*N).prime_divisors()
    k = data['k']
    d = data['d']
    ap = data['ap']

    if verbose:
        print("N = {}".format(N))
        print("k = {}".format(k))
        print("d = {}".format(d))
        print("S = {}".format(S))

    def tr(p): # values in GF(3)
        return F3(ap[prime_pi(p)-1])
        
    # Step 1: compute the determinant character

    chilist = data['chi']
    G = DirichletGroup(N, GF(3))
    
    # Select the char mod 3 whose values macth the data:
    chi = next(g for g in G if all([g(a)==b for a,b in chilist]))

    def det_char(p): # values in GF(3)^*
        a = F3(p)**(k-1) * chi(p)
        return a

    T1, A, decoder = get_T1data(S)
    D = decoder([0 if det_char(p)==1 else 1 for p in T1])
    if verbose:
        print("discriminant = {}".format(D) + (" (cyclotomic)" if D==-3 else ""))

    # Since these are odd representations, the discriminant will
    # always be negative, and in particular not 1:
    assert D<0
    
    # Step 2: find all possible quartics

    # Since D<0 we seek extensions of Q which are S4 or D4 or V4 and with
    # discriminant field Q(sqrt(D))
    
    quartics = get_quartics(S, D)
    if verbose:
        print("{} candidate quartics".format(len(quartics)))
        #print(quartics)

    # Step 3: test irreducibility, cutting down the possible quartics
    # (possibly to none).

    quartics2 = []
    irred = False
    for f in quartics:
        p =  next(p for p in Primes() if (not p in S) and mod_p_fact_degs(f,p)==[2,2])
        if det_char(p)==1 and tr(p)==0:
            quartics2.append(f)
            if verbose and not irred:
                print("Irreducible via p={}".format(p))
            irred = True
        # else:
        #     if verbose:
        #         print("Discarding {} using p={}".format(f,p))

    # If all quartics have been eliminated, the representation is reducible:
    
    if not irred:
        print("{} mod {}: Reducible".format(label, 3))
        data['reducible'] = True
        return data

    # Now we try to eliminate more remaining quartics by matching
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
                 
    maxp = 100
    Sx = Set(sum([f.discriminant().support() for f in quartics2], S))
    #print("Not using primes in {}".format(Sx))
    for p in primes(maxp):
        if p==2 or p in Sx:
            continue
        (t, d) = (int(tr(p)!=0), det_char(p))
        # for f in quartics2:
        #     print("p={}, f={}, [f modp]={}, (t,d)={} -> {}".format(p,f,mod_p_fact_degs(f,p),(t,d), fact_pats[(t,d)]))
        quartics2 = [f for f in quartics2 if mod_p_fact_degs(f,p) in fact_pats[(t,d)]]
        # if verbose:
        #     print("After checking p={}, {} possible quartics remain".format(p,len(quartics2)))
        if not quartics2: break
    if verbose:
        print("After testing all p<{}, {} possible quartics remain".format(maxp,len(quartics2)))
        
    if not quartics2:
        # If we get here, our list of quartics cannot have been complete
        data['pol'] = None
        data['gal'] = None
        data['reducible'] = None
        print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        print(" label = {} has a problem: reducibility not established but no quartic matches".format(label))
        #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        raise RuntimeError
        return data
        
    
    # Otherwise, if just one quartic remains, the representation is
    # irreducible with this kernel polynomial:
    
    if len(quartics2)==1:
        pol = quartics2[0]
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
        
    # Step 4: Otherwise we find additional distinguishing primes.
        
    if verbose:
        print("Irreducible, polynomial is one of {}:  {}".format(len(quartics2),quartics2))
        print("Computing distinguishing test prime set T0")
    T0, vlist = get_T0mod3data(S,D,quartics2)
    if verbose:
        print("test prime set T0: {}".format(T0))
        print("vlist = ")
        for v,q in zip(vlist,quartics2):
            print("v={} for quartic {}".format(v,q))
            
    # Compute test vector.  Here ap=+1,-1 map to 1 and 0 to 0
    v = [int(tr(p0)!=0) for p0 in T0]
    if verbose:
        print("test vector = {}".format(v))
        
    # NB the vectors in vlist are distinct by construction, and v should equal exactly one of them:
    if v in vlist:
        i = vlist.index(v)
        pol = quartics2[i]
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
        # If we get here, out list of quartics cannot have been complete
        data['pol'] = None
        data['gal'] = None
        data['reducible'] = None
        print("Problem: reducibility not established but no quartic matches")
        print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
        #raise RuntimeError
        return data
        
def run(fname, dir=DATA_DIR, no_repeats=False, outfilename=None, verbose=False):
    ell = 3
    alldata = read_data(fname, ell, dir=dir)
    print("finished reading data: {} forms mod 3".format(len(alldata)))
    if no_repeats:
        alldata = [data for data in alldata if data['i']==1]
        print(" -- only processing {} distinct forms".format(len(alldata)))
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
            print(display_string(res1, ell))

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
