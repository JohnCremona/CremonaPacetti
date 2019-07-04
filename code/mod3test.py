from sage.all import QQ, ZZ, QuadraticField, GF, NumberField, DirichletGroup

# Function to read one line of Drew's output

def read1line(L):
    if L[0]!='<':
        return None
    L = L.replace('<','[')
    L = L.replace('>',']')
    L = L.replace(']],',']]')
    L = eval(L)
    assert len(L)==6
    data = {}
    data['N'] = L[0] # level
    data['k'] = L[1] # weight
    data['i'] = L[2] # index of character
    data['d'] = L[3] # degree of coefficient field (=1)
    data['ap'] = dict(L[4])
    data['chilist'] = L[5]
    return data

def read_data(filename='mod-3-reps.txt'):
    alldata = []
    for L in open(filename).readlines():
        data = read1line(L)
        if data:
            alldata.append(data)
    return alldata

from T0T1T2 import get_T1
from T0mod3 import get_T0_mod3
from S4 import abs_irred_extensions_with_quadratic, irred_extensions_with_quadratic
assert abs_irred_extensions_with_quadratic

# Process a single form data packet:

quartic_lists = {}
def get_quartics(S, D):
    global quartic_lists
    SS = tuple(S)
    if not (SS,D) in quartic_lists:
        quartic_lists[(SS,D)] = irred_extensions_with_quadratic(QQ,S,QuadraticField(D))
    return quartic_lists[(SS,D)]

def check1form(data, verbose=False):
    N = ZZ(data['N'])
    S = (3*N).prime_divisors()
    k = data['k']
    d = data['d']
    if verbose:
        print("N = {}".format(N))
        print("k = {}".format(k))
        print("d = {}".format(d))
        print("S = {}".format(S))

    # compute the determinant character
    T1, A, decoder = get_T1(QQ,S)
    chilist = data['chilist']
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
    quartics = irred_extensions_with_quadratic(QQ,S,QuadraticField(D))
    if verbose:
        print("candidate irreducible quartics: {}".format(quartics))
    _, T0, vlist = get_T0_mod3(QQ,S,quartics)
    if verbose:
        print("test prime set T0: {}".format(T0))

    # Compute test vector.  Here ap=+1,-1 map to 1 and 0 to 0
    ap = data['ap']
    v = [int(ap[p]!=0) for p in T0]
    if verbose:
        print("test vector = {}".format(v))
    if v in vlist:
        i = vlist.index(v)
        pol = quartics[i]
        id = pol.galois_group().id()
        gal = 'S4' if id==[24,12] else 'C4' if id==[4,1] else 'D4'
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        return data,'irreducible', pol, gal
    if verbose:
        print("Reducible")
        print("----------------------------------------------------------")
    return data,'reducible'

# 13 irreducible, all S4
# 17 reducible

def run():
    alldata = read_data()
    print("finished reading data")
    res = [check1form(data, verbose=True) for data in alldata]
    print("finished checking")
    reds = [r for r in res if 'reducible' in r]
    nreds = len(reds)
    irreds = [r for r in res if 'irreducible' in r]
    nirreds = len(irreds)
    print("{} forms are irreducible and {} are reducible".format(nreds,nirreds))
    S4s = [r for r in res if 'S4' in r]
    nS4 = len(S4s)
    print("{} forms are irreducible with splitting field S4:".format(nS4))
    def display(r):
        pol = r[2]
        disc = NumberField(pol,'a').discriminant().factor()
        data = r[0]
        print("N={}, k={}, d={}, f={} defining {} field with discriminant {}".format(
            data['N'],data['k'],data['d'],r[2],r[3],disc))
    for r in S4s:
        display(r)
    D4s = [r for r in res if 'D4' in r]
    nD4 = len(D4s)
    print("{} forms are irreducible with splitting field D4:".format(nD4))
    for r in D4s:
        display(r)
    C4s = [r for r in res if 'C4' in r]
    nC4 = len(C4s)
    print("{} forms are irreducible with splitting field C4:".format(nC4))
    for r in C4s:
        display(r)
