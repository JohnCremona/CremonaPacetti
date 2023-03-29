# Function to read one line of Drew's output

from sage.all import QQ, prime_pi

from T0T1T2 import get_T0
from C2C3S3 import S3_extensions, C3S3_extensions
from read_modell_data import read_data, DATA_DIR

# We will see tghe same set S of primes for different levels, and only want to construct the relevant cubics once so we cache them here:
#

# We only reset the cache if it is not set e.g. on first readong this file, so we can reread the file for a second run with non of the time-consuming# cubic searching.

try:
    assert len(cubic_lists)
except:
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

try:
    assert len(T0data)
except:
    T0data = {}

def get_T0data(S, cubics):
    global T0data
    SS = tuple(S)
    if not SS in T0data:
        _, T0, vlist = get_T0(QQ,S,cubics)
        T0data[SS] = [T0, vlist]
    return T0data[SS]

# Process a single form data packet:

def check1form(data, verbose=False):
    assert data['ell'] == 2
    N = data['N']
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
    T0, vlist = get_T0data(S,cubics)
    T0_indices = [prime_pi(p)-1 for p in T0]
    if verbose:
        print("test prime set T0: {}".format(T0))

    # Compute test vector.
    ap = data['ap']
    v = [int(ap[ip]) for ip in T0_indices]
    if verbose:
        print("test vector = {}".format(v))
    if v in vlist:
        i = vlist.index(v)
        data['pol'] = pol = cubics[i]
        id = pol.galois_group().id()
        data['gal'] = gal = 'S3' if id==[6,1] else 'C3'
        if verbose:
            print("Irreducible: splitting field polynomial = {} with group {}".format(pol,gal))
            print("----------------------------------------------------------")
        data['reducible'] = False
        return data
    if verbose:
        print("Reducible")
        print("----------------------------------------------------------")
    data['reducible'] = True
    return data

def display_string(data, ell=2):
    """Display splitting field info for one rep as a string
    """
    if data['reducible']:
        return "{} mod {}:  reducible".format(data['label'], ell)

    pol = data['pol']
    # if pol.is_irreducible():
    #     L = NumberField(pol,'a')
    # else:
    #     L = pol.splitting_field('a')
    # if pol.base_ring() is QQ:
    #     disc = L.discriminant().factor()
    # else:
    #     disc = L.relative_discriminant().factor()
    detdisc = pol.discriminant().squarefree_part()
    if detdisc%4 != 1:
        detdisc*=4
    if ell==2:
        return "{} mod {}:  image {}, splitting field polynomial {}; determinant field discriminant {}".format(
            data['label'], ell, data['gal'], pol, detdisc)
    else:
        return "{} mod {}:  linear image {}, splitting field polynomial {};\n           projective image {}, splitting field polynomial {}; determinant field discriminant {}".format(
            data['label'], ell, data['lingal'], data['octic'].factor(), data['gal'], pol.factor(), detdisc)

def display_all(datalist, ell=2, fname=None):
    """Display splitting field info for a list of irreducibles, either to
    a file (if fname is not None) or to the screen
    """
    if fname:
        with open(fname, 'a') as outfile:
            for data in datalist:
                outfile.write(display_string(data, ell)+"\n")
    else:
        for data in datalist:
            print(display_string(data, ell))
    
def run(fname, dir=DATA_DIR, no_repeats=False, outfilename=None, verbose=False):
    ell = 2
    alldata = read_data(fname, ell, dir=dir)
    print("finished reading data: {} newforms".format(len(alldata)))
    if no_repeats:
        alldata = [data for data in alldata if data['i']==1]
        print(" -- only processing {} distinct forms".format(len(alldata)))
    nreds = 0   # count of reducibles
    nirreds = 0 # count of irreducibles
    gal_counts = {'S3':0, 'C3':0}   # counts of irreducibles with projective image S3, C3
    nC3s = 0    # count of irreducibles with C3 image
    nS3s = 0    # count of irreducibles with S3 image

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

    print("{} lines written to {}".format(nreds+nirreds, outfilename))
    print()
    print("{} forms are reducible and {} are irreducible".format(nreds,nirreds))
    for gal in gal_counts:
        print("{} forms are irreducible with splitting field {}".format(gal_counts[gal], gal))

