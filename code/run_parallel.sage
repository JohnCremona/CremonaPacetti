from os import system, path, getpid
PATH_TO_GP = "/home/apacetti/bin"
GP = os.path.join(PATH_TO_GP,"gp")
GP_FLAGS = "--default parisizemax=10000M -q"
GP_SCRIPT = "ComputingEllipticCurves2.gp"

def compute_curves(N,flag2isogenies=False,flagconductorsupport=False):
    """Compute elliptic curves with good reduction outside support of N.

    INPUT:

    - N (integer) -- product of primes at which bad reduction is allowed

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
    comm = "echo 'ComputeCurves(%s,%s,%s)' | %s %s %s > %s" % (N,int(flag2isogenies),int(flagconductorsupport),GP,GP_FLAGS,GP_SCRIPT,tempfile)
    #print("Command line = %s" % comm)
    os.system(comm)
    result = file(tempfile).read()
    os.unlink(tempfile)
    #print("gp output = %s" % result)
    result = eval(result) # much easier than parsing but possibly dangerous
    result.sort()
    return result

@parallel(30)
def compute_curves_parallel(params):
    print("Starting N=%s" % params[0])
    return compute_curves(*params)

def compute_curves_multi(Nlist,flag2isogenies=False,flagconductorsupport=False):
    results = compute_curves_parallel([[N,flag2isogenies,flagconductorsupport] for N in Nlist])
    for r in results:
        yield r[1]

# Sample usage:
#
def prime_run(first,last,outfilename):
    of = file(outfilename,mode='w')
    for r in compute_curves_multi(prime_range(first,last+1)):
        if r:
            for ri in r:
                of.write("%s %s\n" % (ri[0],ri[1]))
            of.flush()
    of.close()
