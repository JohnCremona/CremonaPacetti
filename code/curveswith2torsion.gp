\\ Computation of general isogenies
read("isogs.gp");
\\ Computation of 2-isogenies and chains of these
read("isogs2.gp");

/*FORDIV(N,x,seq)=
 { my(P, E);
   P = factor(N); E = P[,2]; P = P[,1];
   forvec( v = vector(#E, i, [0,E[i]]),
   X = factorback(P, v)
   evaluate(seq,x)
 );
 }*/

Fordiv(N,sec)=
	{local(fact,Pr);
	fact=factor(N);
	Pr=fact[,1]~;
	forvec(X=vector(matsize(fact)[1],k,[0,fact[k,2]]),
	    sec(X))}

SzpiroBound(N)=
	{local(fact,Ninfty,expbound,ans);
	fact=factor(N);
	Ninfty=prod(j=1,matsize(fact)[1],if(fact[j,1]==2,2^8,if(fact[j,1]==3,3^5,fact[j,1]^2)));
	expbound=vector(matsize(fact)[1],j,if(fact[j,1]==2,floor(6.1*(log(Ninfty)-log(squarefree(N)/fact[j,1]))/log(fact[j,1])),floor(3*(log(Ninfty)-log(squarefree(N)/fact[j,1]))/log(fact[j,1]))));
	ans=prod(j=1,matsize(fact)[1],fact[j,1]^expbound[j]);
	if(N%2!=0,2^8*ans,ans)
};

/* We consider 2 different cases, whether val_p(b) is even, in which
 case the valuation of the discriminant is twice that of b, or it is
 3, and v_p(Disc)=3. We write the discriminant as Delta=b*A, and run
 through the divisors A of the Discriminant candidates.  The cases
 are: -1 meaning valuation 3, the other even exponents valuations (for
 p \neq 2). At p=2, -2 is case of valuation 4, -1 the case of
 valuation 5, and the others as before.*/

CurvesWith2TorsionOfSupport(N,flag2isogenies,flagConductorsupport)=
	{local(Szp,Primes,loopvector,b,Delta,curves,A,Div,V2T,answer,Elred,M);
	b=A=1;curves=[];
	M=squarefree(N);
	Szp=factor(SzpiroBound(N));
	Primes=Szp[,1]~;
	loopvector=[[-2,Szp[1,2]\2]];
	loopvector=concat(loopvector,vector(matsize(Szp)[1]-1,k,[-1,Szp[k+1,2]\2]));
	forvec(X=loopvector,b=A=Div=1;
	    if(X[1]==-2,b*=2;A*=4,if(X[1]==-1,b*=2;A*=8,b*=Primes[1]^X[1]));
	    if(X[1]==0,Div*=Primes[1]^Szp[1,2]);
	    for(j=2,length(X),
		if(X[j]==-1,b*=Primes[j];A*=Primes[j],
		    b*=Primes[j]^(X[j]);
		    if(X[j]==0,Div*=Primes[j]^Szp[j,2])));
	    fordiv(Div,d,if(issquare(A*d+4*b,&a),curves=concat(curves,x^3+a*x^2+b*x));if(issquare(-A*d+4*b,&a),curves=concat(curves,x^3+a*x^2+b*x));if(issquare(A*d-4*b,&a),curves=concat(curves,x^3+a*x^2-b*x));if(issquare(-A*d-4*b,&a),curves=concat(curves,x^3+a*x^2-b*x))));
\\||issquare(A*d-4*b,&a),&a)||issquare(-(A*d-4*b),&a),print(Div," ",A,"  ",b);
\\	return(curves);
	curves=Set(curves);
	for(k=1,length(Primes),Primes[k]*=kronecker(-1,Primes[k]));
	curves=vector(length(curves),k,Ell(curves[k]));
	curves=ComputeTwists(curves,Primes);
	V2T=curves; 
	if(flag2isogenies==0,
	    for(k=1,length(curves),
	        V2T=concat(V2T,two_power_isogs(curves[k]))));
	V2T=Set(V2T); answer=[];
	for(k=1,length(V2T),Elred=ellglobalred(ellinit(V2T[k]));
	    if(flagConductorsupport==0,
		if(Elred[1]%2==N%2 && Elred[1]%M==0,answer=concat(answer,[[Elred[1],V2T[k]]])),answer=concat(answer,[[Elred[1],V2T[k]]])));
	answer
};

\\======================================================================	
\\ Stupid routine to remove multiple factors (already in GP?)

squarefree(N)=
	{local(factorization);
	factorization=factor(N)[,1]~;
	prod(i=1,length(factorization),factorization[i])
};

\\======================================================================
\\ The output in most routines is a cubic polynomial. This script puts
\\ it into a weierstrass equation (and minimal model).


Ell(pol,aux)=aux=ellminimalmodel(ellinit([0,polcoeff(pol,2),0,polcoeff(pol,1),polcoeff(pol,0)]));vector(5,k,aux[k]);

\\======================================================================
\\ Given a vector of elliptic curves, and a vector of discriminants,
\\ computes twists for the given conductors. If twists by -4,8,-8,
\\ first prime element must be 2.

ComputeTwists(V,W)=
	{my(aux,MMC);
	aux=V;
	if(W[1]==2,
	    for(k=1,length(aux),MMC=ellminimalmodel(ellinit(ellquadtwist(aux[k],-4)));
	    aux=concat(aux,[vector(5,j,MMC[j])]));
	    for(k=1,length(aux),MMC=ellminimalmodel(ellinit(ellquadtwist(aux[k],8)));
	    aux=concat(aux,[vector(5,j,MMC[j])]));
	    W=vectorkill(W,1));
	for(k=1,length(W),
	    for(j=1,length(aux),MMC=ellminimalmodel(ellinit(ellquadtwist(aux[j],W[k])));
	    aux=concat(aux,[vector(5,i,MMC[i])])));
	Set(aux)
};

\\======================================================================
\\ This routine computes the coeficients of a quadratic twist of an
\\ elliptic curve.

ellquadtwist(E,D)=
	{if(D%4!=0&&D%4!=1,error("not a discriminant"));
	[E[1]*D,D*(E[2]-E[1]^2/4*(D-1)),E[3]*D^2,D^2*(E[4]-E[1]*E[3]/2*(D-1)),
	D^3*(E[5]-E[3]^2/4*(D-1))]
};

\\======================================================================
\\ Given a vector, and an index i, removes the i-th coordinate

vectorkill(v,i)=vector(length(v)-1,x,if(x<i,v[x],v[x+1]));
