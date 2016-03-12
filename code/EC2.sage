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

#Input: (1) Id the conductor ideal.
#	(2) A constant for the Szpiro bound.

def EC(Id,const): 
    
    K=Id.ring()
    twofact=[x for x,e in K.factor(2)]
    Fact=[x for x in K.factor(Id)]
    Fact=[x[0] for x in Fact]
    primes=[p.gen(1) for p in Fact]
    curves=[]
    
    UK = UnitGroup(K)
    u=[1]
    for t in UK.gens_values():
        if t.multiplicative_order()!=+Infinity:
            v=[]
            for j in range(t.multiplicative_order()):
                for k in range(len(u)):
                    v.append(u[k]*(t**j))
            u=v[:]


    ## We create Szpiro constant depending on the maximum discriminant

    szp=const
    for j in primes:
        if (norm(j)%2==0):
            szp *= RR(norm(j))**(8*6.1)  
        elif (norm(j)==0):
            szp *= RR(norm(j))**(5*6.1)
        else:
            szp *= RR(norm(j))**(12.1)
    for j in twofact:
    	if not (Id/j).is_integral():
	    szp *= RR(norm(j))**8
	    primes = primes+[j.gen(1)]
	    Fact = Fact+[j]
#    print(szp)
    szpb= sqrt(szp)   ## bound on b since b^2 divides D

    
    try:
        ai = [RR(p.norm().abs()).log() for p in primes]
    except AttributeError:
        ai = [RR(p).log() for p in primes]
    BB = szpb.log()
    
    # We start checking that the number of primes dividing b ar at
    # least half of the total number of primes.
    # b will be the divisor as in the pdf file.  We split the possible
    # discriminants as b*D, where D will be the part that is prime to
    # b. The possible factorizations of the discriminant whose primes
    # divide b is denoted D1 (so is a vector). This has a unique
    # option (given b) if the prime does not divide 2.
    # primes1 will be the set of primes that divide D (i.e. do not
    # divide b), where we do not have an exact exponent in the
    # discriminant (there are more cases if the prime divides 2).

    
    for v in bounded_iterator(ai,BB):
        n=0
        for j in range(len(primes)):
            if v[j]==0:
                n+=1
		
        if n <= len(primes)/2:    
            b=1
            primes1=[]
            D1=[1+0*K.an_element()]    
            for j in range(len(primes)):    
                if v[j]==0:
                    primes1.append(primes[j])
		else:
		    b*=primes[j]**v[j]
                if v[j]==1:

      # This case gives the exact valuation unless the primes divides 2, in which case there are more possibilities depending on the ramification degree of the prime.

                    if (norm(primes[j])%2==0) :  
                        n=Fact[j].ramification_index()
                        D2=[]
			for k in D1:
			    D2.append(primes[j]^(2*n+3)*k)       
			    for l in range(n):
                                D2.append(primes[j]^(2*l+4)*k)
                        D1=D1+D2            
                    else:    #now the prime does not divide 2, so the valuation is 1
                        D2=[]
                        for k in D1:
                            D2.append(primes[j]*k)
                        D1=D1+D2
            for k in D1:            
                for s in bounded_prime_iterator(primes1,szp/(norm(k)*norm(b)**2)):
                        for t in u:
                            for r in u:
                                d=t*k*s+4*r*b
                                if is_square(d):
                                    E=EllipticCurve([0,sqrt(d),0,r*b,0])
                                    curves.append(E)
                                    curves=curves+[x.codomain() for x in E.isogenies_prime_degree(2)]
                                    
    for p in primes:
        curves1=curves[:]
        for E in curves1:          
            curves.append(E.quadratic_twist(p))
    curves1=curves[:]
    for l in UK.gens_values():
       if l!=1:
            for E in curves1:
                curves.append(E.quadratic_twist(l))
		
    return curves 
