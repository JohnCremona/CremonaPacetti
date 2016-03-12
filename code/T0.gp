\r ComputingEllipticCurves.gp

get_cubics(N) = concat(C3extensions(N),S3extensions(N))

lam(f,p) = #polrootsmod(f,p)==0

lamvec(f,plist) = vector(#plist,j,lam(f,plist[j]))

\\ return indices i<j with vv[i]==vv[j], or 0 if they are distinct:
{
equal_vecs(vv) =
local(n,i,j);
n = #vv;
for(i=1,n-1,for(j=i+1,n,if(vv[i]==vv[j],return([i,j]))));
return(0)
}

\\ return a prime not dividing N modulo which f is irreducible:
{
get_p_1(f,N) =
local(p);
forprime(p=2,,if((N%p)!=0,if(lam(f,p),return(p))));
return(0)
}

\\ return a prime not dividing N modulo exactly one of f,g is irreducible:
{
get_p_2(f,g,N) =
local(p);
forprime(p=2,,if((N%p)!=0,if(lam(f,p)!=lam(g,p),return(p))));
return(0)
}

{
get_T0(N) =
local(flist,n,plist,vlist,vlist0,ij,i,j);
flist = get_cubics(N);
flist0 = concat(flist,x^3);
n = #flist;
plist = [];
vlist = vector(n+1,j,lamvec(flist0[j],plist));
ij = equal_vecs(vlist);
print("With plist=",plist," vlist=",vlist," ij=",ij);
while(ij,
i=ij[1]; j=ij[2];
if(j>n,p=get_p_1(flist[i],N),p=get_p_2(flist[i],flist[j],N));
plist=concat(plist,[p]);
vlist = vector(n+1,j,lamvec(flist0[j],plist));
ij = equal_vecs(vlist);
print("With plist=",plist," vlist=",vlist," ij=",ij);
);
vlist = vector(n,j,lamvec(flist[j],plist));
return([flist,plist,vlist])
}

