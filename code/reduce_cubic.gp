\\ ---------------  GP code  ---------------------------------------
\\
\\======================================================================
\\ Reduction of binary real cubics with negative discriminant,
\\ following J.E.Cremona, Reduction of binary cubic and quartic forms,
\\ LMS JCM 2(1999), 62-92.
\\======================================================================

\\ abcd = [a,b,c,d] are the coefficients of ax^3+bx^3+cx+d

\\ Define the coefficients of the covariant positive definite
\\ quadratic (with respect to basis alpha^2,alpha,1 where alpha is the
\\ real root):

h0(abcd) =
	 {my(a,b,c); a=abcd[1]; b=abcd[2]; c=abcd[3];
          [9*a^2, 6*a*b, 6*a*c-b^2];
}

h0x(abcd,x) =
	 {my(uvw); uvw = h0(abcd);
         (uvw[1]*x+uvw[2])*x+uvw[3];
}

h1(abcd) =
	 {my(a,b,c); a=abcd[1]; b=abcd[2]; c=abcd[3];
          [6*a*b, 6*(b^2-a*c), 2*b*c];
}

h1x(abcd,x) =
	 {my(uvw); uvw = h1(abcd);
         (uvw[1]*x+uvw[2])*x+uvw[3];
}

h2(abcd) =
	 {my(a,b,c,d;); a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4];
          [3*a*c, 3*(b*c-3*a*d), 2*c^2-3*b*d];
}

\\ The norm from K(alpha) to K of an element with coefficients uvw
\\ (where K is the field containing a,b,c,d):

norm3(abcd,uvw) = polresultant(Pol(abcd),Pol(uvw))/abcd[1]^2;

\\ C1=N(h2-h0), C2=N(h0-h1), C3=N(h0+h1) as defined in the paper, and
\\ C4=N(h1).  A form is reduced if
\\ C1>0, C2>=0, C3>0  (i.e. h2 > h0 >= h1 > -h0),  or
\\ C1=0, C2>=0, C4>=0 (i.e. h2 = h0 >= h1 >=0).

\\ The following define the quantities C1,...,C4, but it is quicker in
\\ practice to compute these once and for all as polynomials in
\\ a,b,c,d.  To make sure that we have entered the formulas correctly wo
\\ check that these agree.

xC1(abcd) = norm3(abcd,h2(abcd)-h0(abcd));
xC2(abcd) = norm3(abcd,h0(abcd)-h1(abcd));
xC3(abcd) = norm3(abcd,h0(abcd)+h1(abcd));
xC4(abcd) = norm3(abcd,h1(abcd));

a;b;c;d;

C1(abcd) =
	 {my(a,b,c,d,b2,b3,b4,b5,b6,a2,a3,a4,c2,c3,c4,c5,c6,d2,d3,d4,ac,bd);
		a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4]; b2=b^2;
              	b3=b*b2; b4=b*b3; b5=b*b4; b6=b*b5; a2=a^2; a3=a*a2;
              	a4=a*a3; c2=c^2; c3=c*c2; c4=c*c3; c5=c*c4; c6=c*c5;
              	d2=d^2; d3=d*d2; d4=d*d3; ac=a*c; bd=b*d;

              -108*b3*a2*d - 3*b4*c2 + 54*a2*c4 + 18*b5*d +
              243*a2*d2*b2 - 54*b3*ac*d - 162*bd*c2*a2 - 54*a3*c3 +
              486*a3*bd*c + 3*c4*b2 - 18*c5*a + 54*c3*a*bd -
              243*d2*a2*c2 + 162*d2*ac*b2 + 2*c6 - 729*a4*d2 - 2*b6 +
              18*b4*ac - 27*a2*b2*c2 + 729*d4*a2 + 54*b3*d3 +
              108*c3*d2*a - 18*c4*bd + 27*d2*c2*b2 - 486*d3*ac*b -
              54*d2*b4
};

C2(abcd) = 
	 {my(a,b,c,d,b2,b3,b4,b5,b6,a2,a3,a4,c2,c3,c4,c5,c6,d2,d3,d4,ac,bd);
	 a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4]; b2=b^2;
   	 b3=b*b2; b4=b*b3; b5=b*b4; b6=b*b5; a2=a^2; a3=a*a2; a4=a*a3;
   	 c2=c^2; c3=c*c2; c4=c*c3; c5=c*c4; c6=c*c5; d2=d^2; d3=d*d2;
   	 d4=d*d3; ac=a*c; bd=b*d;

   -(-108*b3*a2*d + 12*b4*c2 - 216*a2*c4 - 72*b5*d - 486*a3*c2*d +
    270*a2*c3*b - 90*b3*c2*a - 972*a2*d2*b2 + 216*b3*ac*d +
    648*bd*c2*a2 - 54*a3*c3 + 486*a3*bd*c - 16*c3*b3 + 216*d2*b3*a
    + 72*d*b4*c + 72*c4*b*a + 216*d*c3*a2 -
    432*d*b2*a*c2 - 729*a4*d2 - 2*b6 + 18*b4*ac - 27*a2*b2*c2 +
    6*b5*c - 648*b2*c*a2*d + 162*a*d*b4 + 1458*a3*d2*b)
};

C3(abcd) = 
	 {my(a,b,c,d,b2,b3,b4,b5,b6,a2,a3,a4,c2,c3,c4,c5,c6,d2,d3,d4);
	 a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4]; b2=b^2;
 	 b3=b*b2; b4=b*b3; b5=b*b4; b6=b*b5; a2=a^2; a3=a*a2; a4=a*a3;
  	 c2=c^2; c3=c*c2; c4=c*c3; c5=c*c4; c6=c*c5; d2=d^2; d3=d*d2;
  	 d4=d*d3;

  108*b3*a2*d - 12*b4*c2 + 216*a2*c4 + 72*b5*d - 486*a3*c2*d +
    270*a2*c3*b - 90*b3*c2*a + 972*a2*d2*b2 - 216*b3*c*a*d -
    648*b*c2*a2*d + 54*a3*c3 - 486*a3*d*c*b - 16*c3*b3 + 216*d2*b3*a +
    72*d*b4*c + 72*c4*b*a + 216*d*c3*a2 - 432*d*b2*a*c2 + 729*a4*d2 +
    2*b6 - 18*b4*a*c + 27*a2*b2*c2 + 6*b5*c - 648*b2*c*a2*d +
    162*a*d*b4 + 1458*a3*d2*b
};

C4(abcd) =
         {my(a,b,c,d);
         a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4];
         a2=a^2; d2=d^2;
         b2=b^2; b3=b*b2; b4=b2^2;
         c2=c^2; c3=c*c2; c4=c2^2;
         27*d*c3*a2 + (27*d2*b3 - 54*d*c2*b2 + 9*c4*b)*a + (9*d*c*b4 - 2*c3*b3)
};

print1("C1 formula: ");
if(C1([a,b,c,d])==xC1([a,b,c,d]), print("OK"), print("bad"));
print1("C2 formula: ");
if(C2([a,b,c,d])==xC2([a,b,c,d]), print("OK"), print("bad"));
print1("C3 formula: ");
if(C3([a,b,c,d])==xC3([a,b,c,d]), print("OK"), print("bad"));
print1("C4 formula: ");
if(C4([a,b,c,d])*8==xC4([a,b,c,d]), print("OK"), print("bad"));

invert(abcd) = [-abcd[4],abcd[3],-abcd[2],abcd[1]];
negate(abcd) = [-abcd[1],abcd[2],-abcd[3],abcd[4]];

translate(abcd,k) =
          {my(a,b,c,d,b1,c1,d1);
	  a=abcd[1]; b=abcd[2]; c=abcd[3]; d=abcd[4];
	  b1 = 3*k*a + b;
	  c1 = k*(3*k*a + 2*b) + c;
	  d1 = k*(k*(k*a + b) + c) + d;
	  [a,b1,c1,d1]
};

real_root(abcd) =
          {my(f,rr,alpha);
           f=Pol(abcd);
           rr=polroots(f);
           alpha=rr[1];
           if(imag(alpha)!=0,alpha=rr[2]);
           if(imag(alpha)!=0,alpha=rr[3]);
           real(alpha);
};

shift_step(abcd) =
           {my(f,x,a);
           f = Pol(abcd);
           x = variable(f);
           a = (bezout(-2*h0x(abcd,x),f)[1] * h1x(abcd,x)) % f;
           round(subst(a,x,real_root(abcd)));
};

reduce_negative_cubic(f) =
          {my(change,rr,alpha,a,b,c,d,h0,h1,k,abcd,Matrix);
	  abcd = Vec(f,-4); \\ we work with coefficient lists of length 4
          Matrix=matid(2);  \\ holds the cumulative transform
	  change=1;         \\ flags that something has changed
	  while(change,
	      change=0;
	      if(C1(abcd)<0,change=1; \\ inversion needed
                            abcd=invert(abcd);
                            Matrix*=[0,1;-1,0]);
              if(C2(abcd)<0 || C3(abcd)<=0,change=1; \\ translation needed
	           k = shift_step(abcd);
	           if(k!=0,abcd=translate(abcd,k);
                           Matrix*=[1,k;0,1]);
                   \\ the next two loops safeguard against rounding
                   \\ errors in computing k and usually do nothing
	           while(C2(abcd)<0,abcd=translate(abcd,-1);
                                    Matrix*=[1,-1;0,1]);
	           while(C3(abcd)<=0,abcd=translate(abcd,+1);
                                     Matrix*=[1,1;0,1]));
              if((C1(abcd)==0) && (C4(abcd)<0),change=1; \\ flip needed
                  abcd=invert(abcd);Matrix*=[0,1;-1,0]);
	      );
          if(abcd[1]<0,abcd=-abcd);
	  [Pol(abcd),Matrix]
};

