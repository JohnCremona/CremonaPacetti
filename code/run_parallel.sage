from os import system, path, getpid
PATH_TO_GP = "/home/jec/bin"
GP = os.path.join(PATH_TO_GP,"gp")
GP_FLAGS = "--default parisizemax=10000M -q"
GP_SCRIPT = "ComputingEllipticCurves2.gp"

def compute_curves(N,flag1=False,flag2=False):
    """Compute elliptic curves with good reduction outside support of N.

    INPUT:

    - N (integer) -- product of primes at which bad reduction is allowed

    - flag1 (boolean, default False) -- if False, use naive bound in
      2-torsion case, else use Szpiro's bound (not currently
      recommended)

    - flag2 (boolean, default False) -- if True, do not compute twists

    OUTPUT:

    A list of pairs [N,[a1,a2,a3,a4,a6]] = [conductor, a-invariants]

    """
    tempfile = 'tempfile-'+str(N)+'-'+str(getpid())
    comm = "echo 'ComputeCurves(%s,%s,%s)' | %s %s %s > %s" % (N,int(flag1),int(flag2),GP,GP_FLAGS,GP_SCRIPT,tempfile)
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

def compute_curves_multi(Nlist,flag1=False,flag2=False):
    results = compute_curves_parallel([[N,flag1,flag2] for N in Nlist])
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
