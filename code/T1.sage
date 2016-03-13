# Funtion to compute  a set  T1 of primes linearly independent with respect to S

def alpha(p,D):
    return ((1-D.kronecker(p))//2) % 2

def alphalist(p, Dlist):
    return [alpha(p,D) for D in Dlist]

def get_T1(S):
    Sx = [-1] + S
    r = len(Sx)
    N = prod(S,1)
    M = Matrix(GF(2),0,len(Sx))
    T1 = []
    p = 2
    while M.rank() < r:
        p = next_prime(p)
        while p.divides(N):
            p = next_prime(p)
        M1 = M.stack(vector(alphalist(p)))
        if M1.rank() > M.rank():
            M = M1
            T1 = T1 + [p]
    return T1, M

def get_T2(S):
    Sx = [-1] + S
    r = len(Sx)
    r2 = r*(r-1)//2
    N = prod(S,1)
    T2 = {}
    p = 2
    while len(T2)<r+r2:
        p = next_prime(p)
        while p.divides(N):
            p = next_prime(p)
        ro = alphalist(p,Sx)
        ij = Set([i for i,vi in enumerate(ro) if vi])
        if len(ij) in [1,2] and not ij in T2:
            T2[ij] = p
    return T2
