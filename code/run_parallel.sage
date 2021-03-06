from os import system, path, getpid
HOME = os.environ['HOME']
PATH_TO_GP = os.path.join(HOME,'bin')
GP = os.path.join(PATH_TO_GP,"gp")
GP_FLAGS = "--default parisizemax=20000M -q"
GP_SCRIPT = "ComputingEllipticCurves.gp"

def compute_curves(N,torsionflag=0,flag2isogenies=False,flagconductorsupport=False):
    """Compute elliptic curves with good reduction outside support of N.

    INPUT:

    - N (integer) -- product of primes at which bad reduction is allowed

    - torsionflag (0 (default),1, or 2) -- if 1, compute only curves
      with no 2-torsion; if 2, only those with 2-torsion;
      else(default) all curves.

    - flag2isogenies (boolean, default False) -- if False, computes curves including
      two-isogenies. If true avoids computing any kind of isogenies.

    - flagconductorsupport (boolean, default False) -- if False computes ONLY the curves
      whose conductors are supported at ALL primes dividing N and discards
      the intermediate computations. If True, computes all curves whose
      conductor is supported at the set of primes dividing N. Note that
      the default option is faster since it avoids solving many thue equations.

    OUTPUT:

    A list of pairs [N,[a1,a2,a3,a4,a6]] = [conductor, a-invariants]

    """
    tempfile = 'tempfile-'+str(N)+'-'+str(getpid())
    gp_function = "ComputeCurves"
    if torsionflag==1:
        gp_function += "Without2Torsion"
    elif torsionflag==2:
        gp_function += "With2Torsion"

    comm = "echo '%s(%s,%s,%s)' | %s %s %s > %s" % (gp_function,
                                                    N,int(flag2isogenies),int(flagconductorsupport),
                                                    GP,GP_FLAGS,GP_SCRIPT,tempfile)
    #print("Command line = %s" % comm)
    os.system(comm)
    result = file(tempfile).read()
    os.unlink(tempfile)
    #print("gp output = %s" % result)
    if result:
        result = eval(result) # much easier than parsing but possibly dangerous
        result.sort()
        return result
    else:
        print("gp output file for N=%s is empty" % N)
        return [[N,'gp error']]


@parallel(30)
def compute_curves_parallel(params):
    print("Starting N=%s" % params[0])
    sys.stdout.flush()
    return compute_curves(*params)

def compute_curves_multi(Nlist,torsionflag=0,flag2isogenies=False,flagconductorsupport=False):
    results = compute_curves_parallel([[N,torsionflag,flag2isogenies,flagconductorsupport] for N in Nlist])
    for r in results:
        yield r[1]

# Utility functions producing nice output to a file for various ranges of N:

# Iterator over square-free N from first to last; if no_primes
# (default False) is True, prime N will be skipped.
#
def sqf_iterator(first,last,no_primes=False):
    for N in xsrange(first,last+1):
        if N.is_squarefree() and not (no_primes and N.is_prime()):
            yield N

# Iterator over square-free N with exactly k prime factors, from first
# to last.
#
def sqf_k_iterator(first,last,k):
    for N in xsrange(first,last+1):
        if N.is_squarefree() and len(N.factor())==k:
            yield N

# Parallel run over any iterator, output to a file (which will be overwritten).
#
# 'it' is any iterator.
#
# Examples:
#
# (1) to run over primes from p1 to p2 (with & without 2-torsion):
#           run_general(prime_range(p1,p2+1),f)
# (2) to run over all squarefrees from N1 to N2 (no 2-torsion):
#           run_general(sqf_iterator(N1,N2),f,1)
# (3) to run over all non-prime squarefrees from N1 to N2 (only 2-torsion):
#           run_general(sqf_iterator(N1,N2,True),f,2)
# (4) to run over squarefrees with k primes from N1 to N22 (with & without 2-torsion):
#           run_general(sqf_k_iterator(N1,N2,k),f)

# NB in the latter, all curves with bad reduction exactly at p|N will
# be found, not just those with good reducation at all primes not
# dividing N.  For that, use

# (4a) to run over squarefrees with k primes from N1 to N2 including
# curves with good reduction at some primes dividing each N:
#           run_general(sqf_k_iterator(N1,N2,k),f,flagconductorsupport=True)

def run_general(it,outfilename,torsionflag=0,flag2isogenies=False,flagconductorsupport=False):
    of = file(outfilename,mode='w')
    for r in compute_curves_multi(it,torsionflag,flag2isogenies,flagconductorsupport):
        if r:
            for ri in r:
                try:
                    N = ZZ(ri[0])
                    if ri[1]=='gp error':
                        of.write("%s %s\n" % (N,ri[1]))
                    else:
                        a1,a2,a3,a4,a6 = [ZZ(ai) for ai in ri[1]]
                        of.write("%s [%s,%s,%s,%s,%s]\n" % (N,a1,a2,a3,a4,a6))
                except TypeError:
                    print("bad data! line = %s" % ri)
            of.flush()
    of.close()

# Strip non-prime-conductor curves from an output file (for comparison with database)
# Input lines should loook like
#
# 11 [0,-1,1,0,0]
#

def prime_conductor_only(infilename):
    inf=file(infilename)
    outf=file(infilename+".primes",mode='w')
    for L in inf.readlines():
        if ZZ(L.split()[0]).is_prime():
            outf.write(L)
    inf.close()
    outf.close()

# Stand-alone function to process several tempfile's (cat'ed together)
# into an output file.  Written after a parallel run which crashed
# (before the error handling was introduced) leaving 29 others running
# ok, but their gp output files were not processed because the
# controlling Sage function had stopped.
#
def process_tempfiles(inf,outf):
    of = file(outf, mode='w')
    n = 0
    i = 0
    for L in file(inf).readlines():
        r=eval(L)
        ni = len(r)
        n += ni
        i += 1
        print("%s curves read from line %s (%s total so far)" % (ni,i,n))
        for ri in r:
            if ri:
                N = ZZ(ri[0])
                a1,a2,a3,a4,a6 = [ZZ(ai) for ai in ri[1]]
                of.write("%s [%s,%s,%s,%s,%s]\n" % (N,a1,a2,a3,a4,a6))
    of.close()
