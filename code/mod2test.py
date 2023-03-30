# Function to read one line of Drew's output

from sage.all import QQ, prime_pi, primes_first_n

from T0T1T2 import get_T0
from C2C3S3 import S3_extensions, C3_extensions, C2_extensions
from S3disc import get_disc
from read_modell_data import read_data, DATA_DIR

# We will see the same set S of primes for different levels, and only
# want to construct the relevant cubics once so we cache them here.

# The keys for the cache are pairs (S,D) where S is a set of primes and D is square-free, representing a discriminant mod squares.
#

# We only reset the cache if it is not set e.g. on first readong this
# file, so we can reread the file for a second run with non of the
# time-consuming# cubic searching.

# cubic_lists[(S,D)] is a list of monic irreducible cubics with
#    discriminant D mod squares supported on S

try:
    assert len(cubic_lists)
except:
    cubic_lists = {}

def get_cubics(S, D=None):
    """Return a list of monic irreducible cubics with discriminant D mod
    squares supported on S, either for one such D or (if D is None)
    for all possible D.

    """
    global cubic_lists
    SS = tuple(S)
    if D:
        if (SS,D) in cubic_lists:
            CC = cubic_lists[(SS,D)]
        else:
            cubic_lists[(SS,D)] = CC = C3_extensions(QQ,SS) if D.is_square() else S3_extensions(QQ,SS,D)
        return CC
    else:
        return sum((get_cubics(S,D1) for D1 in (f.discriminant().squarefree_part() for f in C2_extensions(QQ,S))), [])

# T0data[(S,cubics)] is [T0,vlist] where T0 is a list of test primes
# and vlist a list of vectors such that a galrep is irreducible with
# polynomial cubics[i] if its test vector is vlist[i]

try:
    assert len(T0data)
except:
    T0data = {}

def get_T0data(S, cubics):
    global T0data
    key = (tuple(S), tuple(cubics))
    if key not in T0data:
        _, T0, vlist = get_T0(QQ,S,cubics)
        T0data[key] = [T0, vlist]
    return T0data[key]

# Process a single form data packet:

def process1form(data, proof=True, verbose=False):
    """Input data is a dict with keys

    'N': conductor
    'k': weight
    'd': dimension
    'S': bad primes
    'ap': list of ap mod ell
    'ell': characteristic prime, always 2 here

    Output is this dict with added keys

    'reducible': True/False
    'pol': cubic polynomial defining spltting field (if irreducible)
    'gal': 'S3' or 'C3' (if irreducible)

    If proof==False then we assume reducibility if all the ap given
    (for good p) are 0 mod 2, otherwise the code wil prove this by
    ensuring that the ap are all even for a rigorously computed test
    test of good primes.

    """
    assert data['ell'] == 2
    N = data['N']
    S = (2*N).prime_divisors()
    k = data['k']
    d = data['d']
    aplist = data['ap']
    if verbose:
        print(f"N = {N}")
        print(f"k = {k}")
        print(f"d = {d}")
        print(f"S = {S}")
        #print(f"ap = {aplist}")

    # First test for irreducibility by looking at the ap mod 2.  Here
    # we have to exclude bad p since we are looking for one odd ap for
    # a good prime p.  If we find one then the galrep is certainly
    # irreducible, otherwise we expect it tobe reducible but will work
    # harder to prove it.

    good_primes = primes_first_n(len(aplist))
    BB = dict([(p,(ap,1)) for  p,ap in zip(good_primes,aplist) if p not in S])
    irreducible = any(ap%2 for ap,np in BB.values())
    if verbose:
        if irreducible:
            print("Irreducible: at least one ap for good p is odd")
        else:
            print("Probably reducible: all known ap for good p are even")

    # In the irreducible case we can compute the splitting field
    # discriminant and then use fewer cubics

    if irreducible:
        if verbose:
            print(" - finding discriminant...")
        D = get_disc(QQ, S, BB)
        if verbose:
            print(f" - discriminant = {D}, finding cubics...")
        cubics = get_cubics(S, D)
        if verbose:
            print(f" - found {len(cubics)} cubics with discriminant {D}")
    else:
        if not proof:
            if verbose:
                print("Reducible")
                print("----------------------------------------------------------")
            data['reducible'] = True
            return data
        if verbose:
            print(f" - finding cubics...")
        cubics = get_cubics(S)
        if verbose:
            print(f" - found {len(cubics)} cubics")

    if verbose:
        print(f"candidate cubics: {cubics}")
    T0, vlist = get_T0data(S,cubics)
    T0_indices = [prime_pi(p)-1 for p in T0]
    if verbose:
        print(f"test prime set T0: {T0}")
    # In order to conclude we must have the value of ap for all p in the test set T0
        
    # Compute test vector.
    try:
        v = [int(aplist[ip]) for ip in T0_indices]
        data['ok'] = True
    except IndexError(f"not enough ap known to conclude! The test set of primes is {T0}"):
        data['ok'] = False
        return data
        
    if verbose:
        print(f"test vector = {v}")
    if v in vlist:
        i = vlist.index(v)
        data['pol'] = pol = cubics[i]
        id = pol.galois_group().id()
        data['gal'] = gal = 'S3' if id==[6,1] else 'C3'
        if verbose:
            print(f"Irreducible: splitting field polynomial = {pol} with group {gal}")
            print("----------------------------------------------------------")
        data['reducible'] = False
        return data
    if verbose:
        print("Reducible")
        print("----------------------------------------------------------")
    data['reducible'] = True
    return data

# NB Both display_string and display_all are imported by mod3test as well as being used here!

def display_string(data, ell=2, concise=True):
    """Display splitting field info for one rep as a string
    """
    if data['reducible']:
        pad1 = pad2 = ""
        if not concise:
            pad1 = f" mod {ell}"
            pad2 = "  "
        return "".join([f"{data['label']}", pad1, ":", pad2, "reducible"])

    pol = data['pol']
    if concise:
        if ell==2:
            line = f"{data['label']}:{data['gal']}:{pol}"
        else:
            line = f"{data['label']}:{data['lingal']}:{data['octic'].factor()}:{data['gal']}:{pol.factor()}"
    else:
        detdisc = pol.discriminant().squarefree_part()
        if detdisc%4 != 1:
            detdisc*=4
        if ell==2:
            line = f"{data['label']} mod {ell}:  image {data['gal']}, splitting field polynomial {pol}; determinant field discriminant {detdisc}"
        else:
            line = "\n".join([f"{data['label']} mod {ell}:  linear image {data['lingal']}, splitting field polynomial {data['octic'].factor()};",
                              f"           projective image {data['gal']}, splitting field polynomial {pol.factor()}; determinant field discriminant {detdisc}"])
    return line

def display_all(datalist, ell=2, concise=True, fname=None):
    """Display splitting field info for a list of irreducibles, either to
    a file (if fname is not None) or to the screen
    """
    if fname:
        with open(fname, 'a') as outfile:
            for data in datalist:
                outfile.write(display_string(data, ell, concise)+"\n")
    else:
        for data in datalist:
            print(display_string(data, ell, concise))
    
def run(fname, dir=DATA_DIR, no_repeats=False, outfilename=None, concise=True, verbose=False):
    ell = 2
    alldata = read_data(fname, ell, dir=dir)
    print("finished reading data: {} newforms".format(len(alldata)))
    if no_repeats:
        alldata = [data for data in alldata if data['i']==1]
        print(" -- only processing {} distinct forms".format(len(alldata)))
    nreds = 0   # count of reducibles
    nirreds = 0 # count of irreducibles
    gal_counts = {'S3':0, 'C3':0}   # counts of irreducibles with projective image S3, C3

    if outfilename:
        with open(outfilename, 'a') as outfile:
            for data in alldata:
                res1 = process1form(data, proof=False, verbose=verbose)
                line = display_string(res1, ell, concise)
                outfile.write(line+"\n")
                if verbose:
                    print(line)

                if res1['reducible']:
                    nreds += 1
                else:
                    nirreds += 1
                    gal_counts[res1['gal']] +=1
    else:
        for data in alldata:
            res1 = process1form(data,  proof=False, verbose=verbose)
            line = display_string(res1, ell, concise)
            print(line)

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

