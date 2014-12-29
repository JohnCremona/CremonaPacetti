default(realprecision,50);
\\verb=0;

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\
\\ Roots of a polynomial!  (not elliptic curve specific)
\\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
polratroots(pol)=
{
local(fx,ans,fxj);
fx=factor(pol); ans=[];
for(j=1,#(fx~),fxj=fx[j,1];
if(poldegree(fxj)==1,
ans=concat(ans,[-polcoeff(fxj,0)/polcoeff(fxj,1)])));
ans;
}

two_torsion(e)= 
{
local(ee,x2s);
ee=ellinit(e);
x2s=polratroots(elldivpol(ee,2));
vector(#(x2s),j,[x2s[j],-ee.a1*x2s[j]-4*ee.a3]);
}

\\ two_isogs(e) finds all curves 2-isogenous to e, returning the curves
\\ in a (posssibly empty) vector.  If it gives the error message
\\ "precision loss in \\truncation" (sent to sterr) try doubling the
\\ precision.

two_isogs(e)= 
{
local(ee,tt,ans,T,xj,t,e2);
ee=ellinit(e,1);
tt=two_torsion(e);
ans=vector(length(tt),j,0);
for(j=1,length(tt),
 xj = 4*tt[j][1];
 t = 3*xj*xj+2*ee.b2*xj+8*ee.b4;
 w = xj*t;
 e2=ellinit([2*ee.a1, 4*ee.a2, 8*ee.a3, 16*ee.a4-5*t, 64*ee.a6-4*ee.b2*t-7*w]);
 ans[j]=vecextract(ellminimalmodel(e2),"1..5"));
ans
}

isin(e,list,n)=
{
local(ans,j);
ans=0;j=1;
while((j<=n)&&(ans==0),ans=(e==list[j]);j=j+1);
ans
}

two_power_isogs(e)=
{
local(ans,i,j,ee,e2);
ans=[e]; \\ list of curves in the class
i=0;     \\ index of last curve processed
j=1;     \\ number of curves in list
while(i<j,i+=1;
        ee=two_isogs(ans[i]);
        for(k=1,length(ee),e2=ee[k];
              if(!isin(e2,ans,j),ans=concat(ans,[e2]);j+=1)));
ans
}

