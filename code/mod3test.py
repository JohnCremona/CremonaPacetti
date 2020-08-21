from sage.all import QQ, QuadraticField, GF, NumberField, DirichletGroup, prime_pi

from read_modell_data import read_data, DATA_DIR
from mod2test import display_string, display_all
assert display_string # for pyflakes, since not used in this file
assert display_all    # for pyflakes, since not used in this file

from T0T1T2 import get_T1
from T0mod3 import get_T0_mod3
from S4 import abs_irred_extensions_with_quadratic, irred_extensions_with_quadratic, irred_extensions
assert abs_irred_extensions_with_quadratic

try:
    assert len(quartic_lists)
except:
    quartic_lists = {}

def get_quartics(S, D=None):
    global quartic_lists
    SS = tuple(S)
    if D==None:
        if not (SS,) in quartic_lists:
            quartic_lists[(SS,)] = irred_extensions(QQ,S)
        return quartic_lists[(SS,)]
    if not (SS,D) in quartic_lists:
        quartic_lists[(SS,D)] = irred_extensions_with_quadratic(QQ,S,QuadraticField(D))
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
    SSD = (tuple(S),D)
    if not SSD in T0mod3:
        # print("New (S,D)")
        _, T0, vlist = get_T0_mod3(QQ,S,quartics)
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
    print("label = {}".format(label))
    N = data['N']
    S = (3*N).prime_divisors()
    k = data['k']
    d = data['d']
    if verbose:
        print("N = {}".format(N))
        print("k = {}".format(k))
        print("d = {}".format(d))
        print("S = {}".format(S))

    # compute the determinant character
    T1, A, decoder = get_T1data(S)
    chilist = data['chi']
    G = DirichletGroup(N, GF(3))
    chi = [g for g in G if all([g(a)==b for a,b in chilist])][0]
    def det_char(p):
        a = p**(k-1) * chi(p)
        return 0 if a%3==1 else 1
    D = decoder([det_char(p) for p in T1])
    if verbose:
        print("discriminant = {}".format(D))

    # Since these are odd representations, the discriminant will
    # always be negative, and in particular not 1:
    assert D<0
    #quartics = abs_irred_extensions_with_quadratic(QQ,S,QuadraticField(D))
    #quartics = irred_extensions_with_quadratic(QQ,S,QuadraticField(D))
    #quartics = irred_extensions(QQ,S)
    #quartics = [g for g in quartics if NumberField(g,'c_').discriminant().prime_to_m_part(3*N) in [1,-1]]
    quartics = get_quartics(S, D)
    if verbose:
        print("{} candidate irreducible quartics: {}".format(len(quartics), quartics))
    fields = [NumberField(q,'c_') for q in quartics]
    t = [not any([F1.is_isomorphic(F2) for F2 in fields if F2!=F1]) for F1 in fields]
    if not all(t):
        print([not any([F1.is_isomorphic(F2) for F2 in fields if F2!=F1]) for F1 in fields])
    for i,q in enumerate(quartics):
        F = NumberField(q,'c_')
        for j,q2 in enumerate(quartics):
            if j<=i:
                continue
            F2= NumberField(q2,'c2_')
            if F.is_isomorphic(F2):
                print("isomorphic fields with quartics {} and {}".format(q,q2))
    if verbose:
        print("Computing test prime set T0")
    T0, vlist = get_T0mod3data(S,D,quartics)
    T0_indices = [prime_pi(p)-1 for p in T0]
    if verbose:
        print("test prime set T0: {}".format(T0))

    # Compute test vector.  Here ap=+1,-1 map to 1 and 0 to 0
    ap = data['ap']
    v = [int(ap[ip]) for ip in T0_indices]
    if verbose:
        print("test vector = {}".format(v))
    if v in vlist:
        i = vlist.index(v)
        data['pol'] = pol = quartics[i]
        id = pol.galois_group().id()
        data['gal'] = gal = 'S4' if id==[24,12] else 'C4' if id==[4,1] else 'D4'
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        data['reducible'] = False
        return data
    if verbose:
        print("Reducible")
        print("----------------------------------------------------------")
    data['reducible'] = True
    print(display_string(data,3))
    return data

# 13 irreducible, all S4
# 17 reducible

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
    print("{} forms are irreducible with splitting field S4:".format(nS4))
    D4s = [r for r in irreds if r['gal']=='D4']
    nD4 = len(D4s)
    print("{} forms are irreducible with splitting field D4:".format(nD4))
    C4s = [r for r in irreds if r['gal']=='C4']
    nC4 = len(C4s)
    print("{} forms are irreducible with splitting field C4:".format(nC4))
    return S4s, D4s, C4s
