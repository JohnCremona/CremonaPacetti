def EC(Id,const): #Id ideal generado por el conductor, const constante en la cota de Szpiro (le estabamos poniendo 1)
    
    K=Id.ring()
    f=[x for x in K.factor(Id)]
    primes=[p.gen(1) for p,e in f]
    #print primes
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
    
    szp=const
    for j in primes:
        szp = szp*norm(j)^(12.1) ## needs adjusting for p|6
    szpb= sqrt(szp)   ## bound on b since b^2 divides D
    
    i=0
    b=1
    v=[0] * len(primes)
    
    while i <= len(primes)-1:
        if i!=0:
            i=0
        b=b*primes[i]
        v[i]=v[i]+1
        
        while norm(b) > szpb:
            b=b/(primes[i]^v[i])
            v[i]=0
            i=i+1
            if i == len(primes):
                break 
            b=b*primes[i]
            norm(b)
            v[i]=v[i]+1

        
        primes1=[]
        D1=[1]
        for j in range(len(primes)):
            if v[j]==0:
                primes1.append(primes[j])
            elif v[j]==1:
                if (2/primes[j]).is_integral() :
                    x=primes[j]
                    n=0
                    D2=D1[:]
                    while (2/x).is_integral():
                        for k in D1:    
                            D2.append(primes[j]^(2*n+2)*k)
                        n=n+1
                        x=x*primes[j]
                    for k in D1:    
                        D2.append(primes[j]^(2*n+1)*k)       
                    D1=D2[:]            
                else:
                    D2=D1[:]
                    for k in D1:
                        D2.append(primes[j]*k)
                    D1=D2[:]
                   
        for k in D1:
            l=0
            D=1
            s=[]
            for j in range(len(primes1)):
                if j==0:
                    s.append(0)
                else: 
                    s.append(1)
                    D=D*primes1[j]                
            D=D*k
                
            while l <= len(primes1)-1:
                if l!=0:
                    l=0
                D=D*primes1[l]
                s[l]=s[l]+1
                while norm(D) > szp/(norm(b)^2):
                    D=D/(primes1[l]^(s[l]-1))
                    s[l]=1
                    l=l+1
                    if l == len(primes1):
                        break 
                    D=D*primes1[l]
                    s[l]=s[l]+1
                if l == len(primes1):
                    break
                
                for t in u:
                    for r in u:
                        a=t*D+4*r*b
                        if is_square(a):             
                            curves.append(EllipticCurve([0,sqrt(a),0,r*b,0]))
    return curves
