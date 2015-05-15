# Input: (1) a list of positive reals a_i  [=log(norm(prime[i]))]
#        (2) a bound BB                    [=log(norm(B))]
#
# Output (one by one as a generator):
#
# all lists [e1,e2,...] such that sum(ei*ai) <= BB

def bounded_iterator(ai, BB):
    if len(ai)==0:
        yield []
    else:
        a = ai[0]
        for e in range(BB/a+1):
            for f in bounded_iterator(ai[1:],BB-e*a):
                yield [e]+f

# Input: (1) a list of ideals pi (or of integers if over QQ)
#        (2) a norm bound B
#
# Output (one by one as a generator):
#
# all ideals b=prod(pi**ei) such that Norm(b) <= B


def bounded_prime_iterator(primes, B):
    try:
        ai = [RR(p.norm().abs()).log() for p in primes]
    except AttributeError:
        ai = [RR(p).log() for p in primes]
    BB = RR(B).log()
    for e in bounded_iterator(ai,BB):
        yield prod([p**ei for p,ei in zip(primes,e)])

