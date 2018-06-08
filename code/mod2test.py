# Function to read one line of Drew's output

from T0T1T2 import get_T0
from C2C3S3 import S3_extensions, C3S3_extensions
from mod3test import read_data

from sage.all import QQ,ZZ,NumberField

# Process a single form data packet:

cubic_lists = {}
def get_cubics(S, include_C3=False):
    global cubic_lists
    SS = tuple(S)
    if not SS in cubic_lists:
        if include_C3:
            cubic_lists[SS] = C3S3_extensions(QQ,S)
        else:
            cubic_lists[SS] = S3_extensions(QQ,S)
    return cubic_lists[SS]

def check1form(data, verbose=False):
    N = ZZ(data['N'])
    S = (2*N).prime_divisors()
    k = data['k']
    d = data['d']
    if verbose:
        print("N = {}".format(N))
        print("k = {}".format(k))
        print("d = {}".format(d))
        print("S = {}".format(S))

    cubics = get_cubics(S, True)

    if verbose:
        print("candidate cubics: {}".format(cubics))
    _, T0, vlist = get_T0(QQ,S,cubics)
    if verbose:
        print("test prime set T0: {}".format(T0))

    # Compute test vector.
    ap = data['ap']
    v = [int(ap[p]) for p in T0]
    if verbose:
        print("test vector = {}".format(v))
    if v in vlist:
        i = vlist.index(v)
        pol = cubics[i]
        id = pol.galois_group().id()
        gal = 'S3' if id==[6,1] else 'C3'
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        return data,'irreducible', pol, gal
    if verbose:
        print("Reducible")
        print("----------------------------------------------------------")
    return data,'reducible'


def run():
    alldata = read_data('mod-2-reps.txt')
    print("finished reading data")
    res = [check1form(data, verbose=False) for data in alldata]
    print("finished checking")
    reds = [r for r in res if 'reducible' in r]
    nreds = len(reds)
    irreds = [r for r in res if 'irreducible' in r]
    nirreds = len(irreds)
    print("{} forms are irreducible and {} are reducible".format(nreds,nirreds))
    def display(r):
        pol = r[2]
        disc = NumberField(pol,'a').discriminant().factor()
        data = r[0]
        print("N={}, k={}, d={}, f={} defining {} field with discriminant {}".format(
            data['N'],data['k'],data['d'],r[2],r[3],disc))
    for r in irreds:
        display(r)
