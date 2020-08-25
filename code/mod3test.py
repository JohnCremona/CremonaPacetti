from sage.all import QQ, QuadraticField, GF, NumberField, DirichletGroup, prime_pi, Primes

from read_modell_data import read_data, DATA_DIR
from mod2test import display_string, display_all
assert display_string # for pyflakes, since not used in this file
assert display_all    # for pyflakes, since not used in this file

from T0T1T2 import get_T1
from T0mod3 import get_T0_mod3, mod_p_fact_degs
from S4 import D4_extensions_with_quadratic_V4, S4_extensions_with_quadratic, V4_extensions_with_quadratic
assert S4_extensions_with_quadratic

try:
    assert len(quartic_lists)
except:
    quartic_lists = {}

def S4D4V4_extensions(S, D, verbose=True):
    # NB we know that D<0 so (a) nontrivial and (b) C4 impossible
    M = QuadraticField(D,'m')
    S4s = S4_extensions_with_quadratic(QQ,S,M)
    assert all([f.discriminant().squarefree_part()==D for f in S4s])
    if verbose:
        print("S={}, D={}: {} S4 quartics".format(S,D,len(S4s)))

    D4s = D4_extensions_with_quadratic_V4(QQ,S,M, sg="V4plus")
    #print("D4 quartic discriminants:")
    #print([f.discriminant().factor() for f in D4s])
    assert all([f.discriminant().squarefree_part()==D for f in D4s])
    if verbose:
        print("S={}, D={}: {} D4 quartics".format(S,D,len(D4s)))

    V4s = V4_extensions_with_quadratic(QQ,S,M)
    # print("V4 quartic discriminants:")
    # print([f.discriminant().squarefree_part() for f in V4s])
    # assert all([f.discriminant().squarefree_part()==D for f in V4s])
    if verbose:
        print("S={}, D={}: {} V4 quartics".format(S,D,len(V4s)))

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

# Process a single form data packet:

def check1form(data, verbose=False):
    assert data['ell'] == 3
    label = data['label']
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

    def tr(p):
        return ap[prime_pi(p)-1]
        
    # Step 1: compute the determinant character

    T1, A, decoder = get_T1data(S)
    chilist = data['chi']
    G = DirichletGroup(N, GF(3))
    chi = [g for g in G if all([g(a)==b for a,b in chilist])][0]

    def det_char(p): # values in {+1,-1} mod 3
        a = p**(k-1) * chi(p)
        return a%3
    
    def det_char_add(p): # values in {0,1} mod 2
        return 0 if det_char(p)==1 else 1

    D = decoder([det_char_add(p) for p in T1])
    if verbose:
        print("discriminant = {}".format(D))

    # Since these are odd representations, the discriminant will
    # always be negative, and in particular not 1:
    assert D<0
    
    # Step 2: find all possible quartics

    # Since D<0 we seek extensions of Q which are S4 or D4 or V4 and with
    # discriminant field Q(sqrt(D))
    
    quartics = get_quartics(S, D)
    if verbose:
        print("{} candidate quartics: {}".format(len(quartics), quartics))
    # fields = [NumberField(q,'c_') for q in quartics]
    # t = [not any([F1.is_isomorphic(F2) for F2 in fields if F2!=F1]) for F1 in fields]
    # if not all(t):
    #     print([not any([F1.is_isomorphic(F2) for F2 in fields if F2!=F1]) for F1 in fields])
    # for i,q in enumerate(quartics):
    #     F = NumberField(q,'c_')
    #     for j,q2 in enumerate(quartics):
    #         if j<=i:
    #             continue
    #         F2= NumberField(q2,'c2_')
    #         if F.is_isomorphic(F2):
    #             print("isomorphic fields with quartics {} and {}".format(q,q2))

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
        else:
            if verbose:
                print("Discarding {} using p={}".format(f,p))

    # If all quartics have been eliminated, the representation is reducible:
    
    if not irred:
        if verbose:
            print("Reducible")
            print("----------------------------------------------------------")
        data['reducible'] = True
        return data

    # Otherwise, if just one quartic remains, the representation is
    # irreducible with this kernel polynomial:
    
    if len(quartics2)==1:
        data['pol'] = pol = quartics2[0]
        if pol.is_irreducible():
            id = pol.galois_group().id()
            data['gal'] = gal = 'S4' if id==[24,12] else 'D4'
        else:
            data['gal'] = gal = 'V4'
        
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        data['reducible'] = False
        print(display_string(data,3))
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
    v = [int(tr(p)!=0) for p in T0]
    if verbose:
        print("test vector = {}".format(v))
        
    # NB the vectors in vlist are distinct by construction, and v should equal exactly one of them:
    if v in vlist:
        i = vlist.index(v)
        data['pol'] = pol = quartics2[i]
        if pol.is_irreducible():
            id = pol.galois_group().id()
            data['gal'] = gal = 'S4' if id==[24,12] else 'D4'
        else:
            data['gal'] = gal = 'V4'
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        data['reducible'] = False
        print(display_string(data,3))
        return data
    else:
        # If we get here, out list of quartics cannot have been complete
        data['pol'] = None
        data['gal'] = None
        data['reducible'] = None
        print("Problem: reducibility not established but no quartic matches")
        raise RuntimeError
        return data
        
def run(fname, dir=DATA_DIR, verbose=False):
    alldata = read_data(fname, 3, dir=dir)
    print("finished reading data: {} newforms".format(len(alldata)))
    res = [check1form(data, verbose=verbose) for data in alldata]
    res.sort(key=lambda r: [r['N'],r['k']])
    print("finished checking")
    reds = [r for r in res if r['reducible']]
    nreds = len(reds)
    irreds = [r for r in res if not r['reducible']]
    nirreds = len(irreds)
    print("{} forms are reducible and {} are irreducible".format(nreds,nirreds))
    S4s = [r for r in irreds if r['gal']=='S4']
    nS4 = len(S4s)
    print("{} forms are irreducible with splitting field S4".format(nS4))
    D4s = [r for r in irreds if r['gal']=='D4']
    nD4 = len(D4s)
    print("{} forms are irreducible with splitting field D4".format(nD4))
    V4s = [r for r in irreds if r['gal']=='V4']
    nV4 = len(V4s)
    print("{} forms are irreducible with splitting field V4".format(nV4))
    return S4s, D4s, V4s

