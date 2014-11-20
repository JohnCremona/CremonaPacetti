default(realprecision,50);
verb=0;

\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\
\\ Roots of a polynomial!  (not elliptic curve specific)
\\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
{
polratroots(pol)=
local(fx,ans);
fx=factor(pol); ans=[];
for(j=1,#(fx~),if(poldegree(fxj=fx[j,1])==1,
ans=concat(ans,[-polcoeff(fxj,0)/polcoeff(fxj,1)])));
ans;
}

{
two_torsion(e)= local(x,ee,x2s,nx2s);
kill(x);
ee=ellinit(e);
x2s=polratroots(x^3+ee.b2*x^2+8*ee.b4*x+16*ee.b6);
nx2s=length(x2s);
\\ standardise order
if(verb,print("unsorted x2s = ",x2s));
if(nx2s>1,x2s=vecextract(x2s,vecsort(abs(x2s),,1)));
\\if(nx2s>1,x2s=vecextract(x2s,vecsort(x2s,,1)));
if(verb,print("sorted x2s = ",x2s));
vector(nx2s,j,[x2s[j]/4,(-ee.a1*x2s[j]-4*ee.a3)/8]);
}

{
two_torsion_check(N,cl,cu,e)= local(x,ee,x2s,nx2s);
kill(x);
ee=ellinit(e);
x2s=polratroots(x^3+ee.b2*x^2+8*ee.b4*x+16*ee.b6);
nx2s=length(x2s);
\\ standardise order
if(nx2s>1,x2s=vecextract(x2s,vecsort(abs(x2s),,1)));
if(verb,print("sorted x2s = ",x2s));
if(length(x2s)==3,
if((abs(x2s[1])==abs(x2s[2]))||(abs(x2s[1])==abs(x2s[3]))||(abs(x2s[2])==abs(x2s[3])),print("e=",N,cl,cu," = ",e," x2s = ",x2s)));
vector(nx2s,j,[x2s[j]/4,(-ee.a1*x2s[j]-4*ee.a3)/8]);
}

\\two_isogs(e) finds all curves 2-isogenous to e, returning the curves
\\in a (posssibly empty) vector.  If verb is set to 1 it prints out
\\what it is doing.  If it gives the error message "precision loss in
\\truncation" (sent to sterr) try doubling the precision.  

{
two_isogs(e)= local(ee,tt,ans,T,xj,t,e2);
ee=ellinit(e,1);
tt=two_torsion(e);
ans=vector(length(tt),j,0);
for(j=1,length(tt),
 xj = 4*tt[j][1];
 t = 3*xj*xj+2*ee.b2*xj+8*ee.b4;
 w = xj*t;
 e2=ellinit([2*ee.a1, 4*ee.a2, 8*ee.a3, 16*ee.a4-5*t, 64*ee.a6-4*ee.b2*t-7*w]);
 e2=ellminimalmodel(e2);
 ans[j]=vector(5,k,e2[k]));
ans
}

\\three_torsion_x(e) returns a list of 0, 1 or 2 x-coords (scaled by 3
\\ to be integral for compatibility with C++ program) which are
\\ roots of the 3-division polynomial 
{
  three_torsion_x(e) =
  x3s=polratroots(x^4+e.b2*x^3+9*e.b4*x^2+27*e.b6*x+27*e.b8);
\\ standardise order
   if(verb,print("unsorted x3s = ",x3s));
   if(length(x3s)>1,x3s=vecextract(x3s,vecsort(x3s,,1)));
   if(verb,print("sorted x3s = ",x3s));
   x3s;
}

\\three_isogs(e) finds all curves 3-isogenous to e, returning the curves
\\in a (posssibly empty) vector.  If verb is set to 1 it prints out
\\what it is doing.  If it gives the error message "precision loss in
\\truncation" (sent to sterr) try doubling the precision.  

{
three_isogs(e)= local(ee,xt3,ans,x3,t,w,e3);
if(verb,print("In three_isogs with e = ",e));
ee=ellinit(e,1);
xt3=three_torsion_x(ee);
if(verb,print("xt3 = ",xt3));
ans=vector(length(xt3),j,0);
for(j=1,length(ans),
      x3 = xt3[j];  \\ = 3*x-coord
      t = (2*x3+ee.b2)*x3+3*ee.b4;
      if(verb,print("t = ",t));
      w = ((10*x3+6*ee.b2)*x3+27*ee.b4)*x3+27*ee.b6;
      if(verb,print("w = ",w));
      e3=ellinit([3*ee.a1, 9*ee.a2, 27*ee.a3, 81*ee.a4-135*t, 729*ee.a6-243*ee.b2*t-189*w]);
      e3=ellminimalmodel(e3);
      ans[j]=vector(5,k,e3[k]));
ans
}

\\lisogs(e,ell) finds all curves ell-isogenous to e where ell is
\\prime, returning the curves in a (posssibly empty) vector.  If verb
\\is set to 1 it prints out what it is doing.  If it gives the error
\\message  "precision loss in truncation" (sent to sterr) try doubling
\\the precision.

\\ This works for all prime l but two_isogs is recommended for l=2

{lisogs(e,ell)=
local(e1,ee,num,ans,w1,w2,tau,a1,a2,a3,a4,a6,b2,b4,b6,c4,c6,cond,ltype,nsubs,ilim,ell2,ell3,ell4,ell6,t,w,z,p,xi,yi,ti,ui,rad4,rad6,ad4,ad6,ee2,gr,cond2,e2);
if(ell==2,return(two_isogs(e)));
if(ell==3,return(three_isogs(e)));
e1=e;
if(length(e)<19,e1=e;ee=ellinit(e),e1=vector(5,j,e[j]);ee=e);
if(verb,print("ell = ",ell),);num=0;ans=vector(3,j,0);
w1=ee.omega[1]; w2=ee.omega[2]; tau=w2/w1;
if(verb,print("w1  = ",w1);print("w2  = ",w2);print("tau = ",tau),);
a1=ee[1]; a2=ee[2]; a3=ee[3]; a4=ee[4]; a6=ee[5];
b2=ee[6]; b4=ee[7]; b6=ee[8]; c4=ee[10]; c6=ee[11];
cond=ellglobalred(ee)[1]; ltype=if(real(tau)==0,2,1);
sgn=if((ltype==1)&&(real(tau)<0),-1,+1);
if(verb>1,print("cond = ",cond,", ltype = ",ltype));
nsubs=if(ell==2,if(ltype==1,1,3),2);
if(verb>1,print("nsubs = ",nsubs));
ilim=if(ell==2,1,(ell-1)/2);
if(verb>1,print("ilim = ",ilim));
ell2=ell*ell; ell3=ell*ell2; ell4=ell2*ell2; ell6=ell2*ell4;
if(verb>1,print("starting isub loop"));
for(isub=1,nsubs,t=0; w=0; if(verb,print("isub = ",isub),);
z=if(ell==2,if(isub==1,w1/ell,if(isub==2,w2/ell,(w1+w2)/ell)),if(isub==1,w1/ell,if(ltype==1,2*I*imag(w2)/ell,w2/ell)));
if(verb,print("z = ",z),);
for(j=1,ilim,p=ellztopoint(ee,j*z); xi=p[1]; yi=p[2];
if(verb,print("[i,xi,yi] = ",[j,xi,yi]),);
ptest=yi^2+a1*xi*yi+a3*yi-(xi^3+a2*xi^2+a4*xi+a6);
if(verb,print("ptest = ",ptest),);
ti=if(ell==2,3*xi*xi + 2*a2*xi + a4 - a1*yi,6*xi*xi + b2*xi + b4);
ui=4*xi*xi*xi + b2*xi*xi + 2*b4*xi + b6;
t=t+ti;w=w+ui+xi*ti);
t=real(t); w=real(w);
if(verb,print("[l,t,w] = ",[ell,t,w]),);
rad4=a4-5*t; rad6=a6-b2*t-7*w;ad4=round(rad4);ad6=round(rad6);
if(verb,print("[rad4,rad6] = ",[rad4,rad6]);print("[ad4,ad6] = ",[ad4,ad6]),);
if((abs(ad4-rad4)<0.0001)&&(abs(ad6-rad6)<0.0001),e2=[a1,a2,a3,ad4,ad6];
ee2=ellminimalmodel(ellinit(e2));cond2=ellglobalred(ee2)[1];
e2=vector(5,j,ee2[j]);
\\if(ee2[2]==2,print(e2);print(ee2));
if((cond==cond2)&&(e1!=e2),num=num+1;ans[num]=e2;
if(verb,print("***[1]***(",ell,") ",[t,w],vector(5,j,e[j]),e2),),),
rad4=rad4*ell4;rad6=rad6*ell6; ad4=round(rad4);ad6=round(rad6);
if(verb,print("[rad4,rad6] = ",[rad4,rad6]);print("[ad4,ad6] = ",[ad4,ad6]),);
if((abs(ad4-rad4)<0.0001)&&(abs(ad6-rad6)<0.0001),e2=[ell*a1,ell2*a2,ell3*a3,ad4,ad6];
ee2=ellminimalmodel(ellinit(e2));cond2=ellglobalred(ee2)[1];
e2=vector(5,j,ee2[j]);
\\if(ee2[2]==2,print(e2);print(ee2));
if((cond==cond2)&&(e1!=e2),num=num+1;ans[num]=e2;
if(verb,print("***[2]***(",ell,") ",[t,w],vector(5,j,e[j]),e2),),),)));
ans=vector(num,j,ans[j]);
ans
}

div(a,b)=b%a==0

{getelllist(ee,cond)=local(ans,jay,num);
ans=vector(12,j,0);
ans[1]=2;ans[2]=3;ans[3]=5;ans[4]=7;num=4;
if(issquarefree(cond),ans=vector(4,j,ans[j]);ans,jay=ee[13];num=5;ans[5]=13;
if((jay==-32768)||(jay==-121)||(jay==-24729001),num=num+1;ans[num]=11,);
if(div(17,cond)&&((jay==-297756989/2)||(jay==-882216989/131072)),num=num+1;ans[num]=17,);
if((jay==-9317)||(jay==-7*(137^3)*(2083^3)),num=num+1;ans[num]=37,);
if(jay==-96^3,num=num+1;ans[num]=19,);
if(jay==-960^3,num=num+1;ans[num]=43,);
if(jay==-5280^3,num=num+1;ans[num]=67,);
if(jay==-640320^3,num=num+1;ans[num]=163,);
ans=vector(num,j,ans[j]);ans)
}
 
{
isin(elem,list,n)=local(ans,j);
ans=0;j=1;
while((j<=n)&&(ans==0),ans=(elem==list[j]);j=j+1);
ans
}

{
index(elem,list,n)=
if(n==0,n=length(list));
for(j=1,n,if(elem==list[j],return(j)));0;
}

\\allisog(e) returns a list of lists, each of the form [l,elist],
\\where elist is a nonempty list of curves l-isogenous to e

{allisog(e)=local(ee,cond,list,nell,num,ans,le);
ee=ellinit(e);
cond=ellglobalred(ee)[1];list=getelllist(ee,cond);nell=length(list);
\\print("list = ",list);
num=0;ans=vector(nell,j,0);for(j=1,nell,le=lisogs(ee,list[j]);
\\print(list[j],": ",le);
if(length(le)>0,num=num+1;ans[num]=[list[j],le],));vector(num,j,ans[j])
}

\\allisog1(e) returns a single list of curves l-isogenous to e
\\for some prime l; no info on the l values is assumed or returned.

{allisog1(e)=local(ee,cond,list,nell,num,ans,le);
ee=ellinit(e);
cond=ellglobalred(ee)[1];list=getelllist(ee,cond);nell=length(list);
num=0;ans=vector(26,j,0);
for(j=1,nell,le=lisogs(ee,list[j]);
for(k=1,length(le),num=num+1;ans[num]=le[k]));
vector(num,j,ans[j])
}

\\allisog1l(e) returns a triple consisting of 
\\(1)a list of primes l for which there is an l-isogeny;
\\(2)a single list of curves l-isogenous to e for some prime l; 
\\(3)a list of the corresponding values of l.
\\no info on the l values is assumed.

{allisog1l(e,ee)=local(cond,list,nell,num,ans,le,list1,nell1,list2);
ee=ellinit(e);
cond=ellglobalred(ee)[1];list=getelllist(ee,cond);nell=length(list);
list2=vector(26,j,0);
num=0;ans=vector(26,j,0);list1=vector(nell,j,0);nell1=0;
for(j=1,nell,le=lisogs(ee,list[j]);
if(length(le)>0,nell1=nell1+1;list1[nell1]=list[j],);
for(k=1,length(le),num=num+1;ans[num]=le[k];list2[num]=list[j]));
[vector(nell1,j,list1[j]),vector(num,j,ans[j]),vector(num,j,list2[j])]
}

\\allisog2(e,list) returns a pair consisting of
\\(1)a single list of curves l-isogenous to e for some prime l in list;
\\(2)a list of the corresponding values of l
\\use when you already know the list of l which occur.

{allisog2(e,list)=local(ee,cond,nell,num,ans,le,lans);
ee=ellinit(e);
nell=length(list);num=0;ans=vector(26,j,0);lans=vector(26,j,0);
for(j=1,nell,le=lisogs(ee,list[j]);
for(k=1,length(le),num=num+1;ans[num]=le[k];lans[num]=list[j]));
[vector(num,j,ans[j]),vector(num,j,lans[j])]
}

\\listisog(e,v) takes a curve e and returns a vector each of whose
\\entries has the form [j,l,e'] where e' is a curve isogenous to e which
\\is l-isogenous to the j'th curve in the list.  The list contains ALL
\\curves isogenous to the original, with the original first.  If v=1
\\it also displays the curves as it finds them for prettier output.

{listisog(e,v)=local(ee,cond,ans,num,t,list,inum,e1);
ee=ellinit(e);
cond=ellglobalred(ee)[1];ans=vector(26,j,0);num=1;ans[1]=e;
if(v,print("Conductor = ",cond),);
if(v,print(1,": ",e),);
fromlist=vector(26,j,0); fromlistl=vector(26,j,0);
t=allisog1l(ee);list=t[1];
for(j=1,length(t[2]),num=num+1;ans[num]=t[2][j];
fromlist[num]=1; fromlistl[num]=t[3][j];
if(v,print(num,": ",ans[num]," from curve number ",1," via l = ",fromlistl[num]),););
inum=1;
while(inum<num,inum=inum+1;e1=ans[inum];t=allisog2(e1,list);
for(j=1,length(t[1]),if(isin(t[1][j],ans,num),,num=num+1;ans[num]=t[1][j];
fromlist[num]=inum; fromlistl[num]=t[2][j];
if(v,print(num,": ",ans[num]," from curve number ",inum," via l = ",fromlistl[num]),))));
ans=vector(num,j,[fromlist[j],fromlistl[j],ans[j]]);ans
}

\\testlist(elist) takes a list of curves and checks that it is closed
\\under isogeny.

{testlist(cond,elist)=n=length(elist);ans=1;
for(j=1,n,e=elist[j];t=allisog1(e);
for(k=1,length(t),if(isin(t[k],elist,n),,print1("!!! Curve ",t[k]," is ");
print(" isogenous to curve ",e," but missing from the list !!!");ans=0)));
if(ans,print("Conductor ",cond," OK"),print("Conductor ",cond," NOT OK"));ans
}

aplist(ee,n)=vector(n,j,ellap(ee,prime(j)))

\\Set nap as a global variable: in the next function, two curves are
\\considered isogenous if their first nap a_p agree.
nap=25;   

{test(cond,elist)=local(n,classes,num,ej,aplists);
n=length(elist);
classes=vector(n,j,0);aplists=vector(n,j,0);
for(j=1,n,ej=ellinit(elist[j]);aplists[j]=aplist(ej,nap));
num=0;
for(j=1,n,if(classes[j]==0,num=num+1;classes[j]=num;
for(k=j+1,n,if(classes[k]==0,if(aplists[j]==aplists[k],classes[k]=num,),)),));
print("conductor ",cond,", ",n," curves",", ",num," classes");
\\for(j=1,num,print("Class ",j,":");
\\for(k=1,n,if(classes[k]==j,print(elist[k]),)));
[cond,classes]
}

\\ \r bdw2357jays.gp

\\ Now the vector jaylist has length 2135 and contains all the j
\\ invariants of the {2,3,5,7} curves.

\\njaylist=length(jaylist);

{newtestlist(cond,elist)=local(n,ans);
n=length(elist);ans=1;
for(j=1,n,e=elist[j];t=allisog1(e);
for(k=1,length(t),e2=t[k];ee2=ellinit(e2);j2=ee2[13];
if(isin(j2,jaylist,njaylist)||(j2==1728)||(j2==0),,print1("!!! Curve ",e2," is ");
print(" isogenous to curve ",e," but missing from the list !!!");ans=0)));
if(ans,print("Conductor ",cond," OK"),print("Conductor ",cond," NOT OK"));ans
}


\\The following converts PARI's coding for Kodaira symbols to mine!
convkod(k)=if(k==1,0,if(k>4,10*(k-4),if(k>0,k,if(k==-1,1,if(k<-4,1-10*(k+4),k+9)))))

{isogtab(N,e,v,r,ntor)=local(elist,ee,plist,nplist,cplist,jayden,kodlist);
print(N);
\\print(e[1]," ",e[2]," ",e[3]," ",e[4]," ",e[5]," ",r," ",ntor);
elist=listisog(e,v);plist=Vec(factor(N)[,1]);nplist=length(plist);
print(length(elist));
for(nc=1,length(elist),jle=elist[nc];edash=jle[3];
print1(edash[1]," ",edash[2]," ",edash[3]," ",edash[4]," ",edash[5]," ");
print1(r," ",ntor," ");
ee=ellinit(edash);d=ee[12];print1(sign(d)," ");
for(j=1,nplist,print1(valuation(d,plist[j])," "));
jayden=denominator(ee[13]);
for(j=1,nplist,print1(valuation(jayden,plist[j])," "));
cplist=vector(nplist,j,0);kodlist=vector(nplist,j,0);
\\print();print(cplist);print(kodlist);
for(j=1,nplist,loc=elllocalred(ee,plist[j]);kodlist[j]=convkod(loc[2]);cplist[j]=loc[4]);
\\print();print(cplist);print(kodlist);
for(j=1,nplist,print1(cplist[j]," "));
for(j=1,nplist,print1(kodlist[j]," "));
print();
);
}

codes=["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z","AA","BB","CC","DD","EE","FF","GG","HH","II","JJ","KK","LL","MM","NN","OO","PP","QQ","RR","SS","TT","UU","VV","WW","XX","YY","ZZ","AAA","BBB","CCC","DDD","EEE","FFF","GGG","HHH","III","JJJ","KKK","LLL","MMM","NNN","OOO","PPP","QQQ","RRR","SSS","TTT","UUU","VVV","WWW","XXX","YYY","ZZZ","AAAA","BBBB","CCCC","DDDD","EEEE","FFFF","GGGG","HHHH","IIII","JJJJ","KKKK","LLLL","MMMM","NNNN","OOOO","PPPP","QQQQ","RRRR","SSSS","TTTT","UUUU","VVVV","WWWW","XXXX","YYYY","ZZZZ","AAAAA","BBBBB","CCCCC","DDDDD","EEEEE","FFFFF","GGGGG","HHHHH","IIIII","JJJJJ","KKKKK","LLLLL","MMMMM","NNNNN","OOOOO","PPPPP","QQQQQ","RRRRR","SSSSS","TTTTT","UUUUU","VVVVV","WWWWW","XXXXX","YYYYY","ZZZZZ"];

{isogtaba(N,cl,e,v,r,ntor)=local(elist,jle,edash,nt);
\\print(e[1]," ",e[2]," ",e[3]," ",e[4]," ",e[5]);
elist=listisog(e,v);
\\print(length(elist));
for(nc=1,length(elist),jle=elist[nc];edash=jle[3];
print1(N,"  ",cl,"  ",nc,"  ");
\\print1(edash);
print1("[",edash[1],",",edash[2],",",edash[3],",",edash[4],",",edash[5],"]");
\\if(nc>1,nt=elltors(ellinit(edash))[1],nt=ntor);print1("\t",r,"\t",nt);
print())}

\\ Produce a table similar to William's:

{allisogtab1(N,cl,e)=local(elist,n,m);
elist=listisog(e,0);
n=length(elist);
m=matid(n);
for(j=1,n,m[j,j]=0);
for(j=2,n,m[elist[j][1],j]=elist[j][2];m[j,elist[j][1]]=elist[j][2]);
m=vector(n,i,m[i,]);
print(N," ",cl," 1 ",e," ",vector(n,j,elist[j][3])," ",m);
}

{allisogtab(N,cl,e,v)= 
local(ee,cond,fromlist,fromlistl,ans,num,t,m,mm,list,inum,e1,e2,l);
ee=ellinit(e);
cond=ellglobalred(ee)[1];
ans=vector(26,j,0);num=1;ans[1]=e;
m=matrix(26,26,i,j,0);
if(v,print("Conductor = ",cond),);
if(v,print(1,": ",e),);
fromlist=vector(26,j,0); fromlistl=vector(26,j,0);
\\ process first curve, get list of l's
t=allisog1l(ee);list=t[1];
\\print("inum=",1,": ",t[2]);
\\ add each curve isog to first to list:
for(j=1,length(t[2]),num=num+1;ans[num]=t[2][j];
fromlist[num]=1; fromlistl[num]=t[3][j];
for(j=1,num-1,m[1,j+1]=t[3][j];m[j+1,1]=t[3][j]));
\\ process each curve in turn, adding isog curves to end of list if new
inum=1;
while(inum<num,inum=inum+1;e1=ans[inum];t=allisog2(e1,list);
if(v,print(inum,": ",e1),);
\\print("inum=",inum,": ",t);
\\mm=matrix(num,num,i,j,m[i,j]);
\\mm=vector(num,i,mm[i,]);
\\print(mm);
for(j=1,length(t[1]),e2=t[1][j];i=index(e2,ans,num);
\\print("j=",j,", i=",i);
l=t[2][j];
if(i==0,num=num+1;ans[num]=e2;
\\print("Adding curve #",num,": ",e2);
\\print("Setting (",num,",",inum,") entry to ",l);
m[inum,num]=l;m[num,inum]=l,
\\print("Setting (",num,",",i,") entry to ",l);
m[i,inum]=l;m[inum,i]=l)));
ans=vector(num,i,ans[i]);
m=matrix(num,num,i,j,m[i,j]);
m=vector(num,i,m[i,]);
print(N," ",cl," 1  ",e," ",ans," ",m);
}

{allisoglist(e)= 
local(ee,cond,fromlist,fromlistl,ans,num,t,m,mm,list,inum,e1,e2,l);
ee=ellinit(e);
cond=ellglobalred(ee)[1];
ans=vector(26,j,0);num=1;ans[1]=e;
\\ process first curve, get list of l's
t=allisog1l(ee);list=t[1];
\\print("inum=",1,": ",t[2]);
\\ add each curve isog to first to list:
for(j=1,length(t[2]),num=num+1;ans[num]=t[2][j]);
\\ process each curve in turn, adding isog curves to end of list if new
inum=1;
while(inum<num,inum=inum+1;e1=ans[inum];t=allisog2(e1,list);
for(j=1,length(t[1]),e2=t[1][j];i=index(e2,ans,num);
l=t[2][j];
if(i==0,num=num+1;ans[num]=e2)));
ans=vector(num,i,ans[i]);
for(j=1,num,print(ans[j]));
}
