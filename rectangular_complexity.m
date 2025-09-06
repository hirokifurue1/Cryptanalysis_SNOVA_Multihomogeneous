
//output possible solving multi-degrees
RM_degree := function(m,n,k,r,o,l)
	PZ<[t]>:=PolynomialRing(RationalField(),l);

    //compute G'(t)
    GG:=Binomial(n,r);
    A:=Set(CartesianProduct([{0..r+1}: i in [1..l]])) diff {<0: i in [1..l]>};
    for d in A do
        if &+[d[i]: i in [1..l]] le r+1 then
            mon:=Binomial(n,r) * &*[Binomial(k+d[i]-1,d[i]): i in [1..l]];

            Ad:=Set(CartesianProduct([{0..d[i]}: i in [1..l]])) diff {<0: i in[1..l]>};

            equ:=&+[(-1)^(&+[b[i]: i in [1..l]]+1)
                *&*[Binomial(m+b[i]-1,b[i]): i in [1..l]]
                *Binomial(n,r+&+[b[i]: i in [1..l]])
                *&*[Binomial(k+d[i]-b[i]-1,d[i]-b[i]):i in [1..l]]
                : b in Ad];

            GG:=GG+&*[t[i]^d[i]:i in [1..l]]*(mon-equ);
        end if;
    end for;

    //compute G(t) from G'(t)
    //only compute coefficients of monomials with multi-degree d with |d|=<r+1 for efficiency
    G:=GG;
    mon_r23:=MonomialsOfDegree(PZ,r+2) join MonomialsOfDegree(PZ,r+3);
    for i in [1..l] do
        for j in [1..l] do
            for c in [1..o] do
                G:=G*(1-t[i]*t[j]);
                mon23 := Set(Monomials(G)) meet mon_r23;
                G1:=&+[mono*MonomialCoefficient(G,mono):mono in mon23];
                G:=G-G1;
            end for;
        end for;
    end for;

    if l eq 1 then

        d1:=2;    
        d_mgd:=[];
        isNegative:=false;
        repeat
            if RationalField()! Coefficient(G,t[1],d1) le 1 then
                d_mgd:=[[d1]];
                isNegative:=true;
            end if;
            d1:=d1+1;
        until isNegative eq true or d1 ge r+2;

    elif l eq 2 then

        d2:=2;    
        d_mgd:=[];
        repeat 
            isNegative:=false;
            d1:=d2;
            cf1:=Coefficient(G,t[2],d2);
            repeat
                if RationalField()! Coefficient(cf1,t[1],d1) le 1 then
                    d_mgd:=d_mgd cat [[d1,d2]];
                    isNegative:=true;
                end if;
                d1:=d1+1;
            until isNegative eq true or d1+d2 ge r+2;
            d2:=d2+1;
        until d1 le d2+1 or d2+d2 ge r+2;

    elif l eq 3 then

        d2:=2;
        d3:=2;    
        d_mgd:=[];
        repeat
            d2:=d3;
            cf2:=Coefficient(G,t[3],d3);
            repeat 
                isNegative:=false;
                d1:=d2;
                cf1:=Coefficient(cf2,t[2],d2);
                repeat
                    if RationalField()! Coefficient(cf1,t[1],d1) le 1 then
                        d_mgd:=d_mgd cat [[d1,d2,d3]];
                        isNegative:=true;
                    end if;
                    d1:=d1+1;
                until isNegative eq true or d1+d2+d3 ge r+2;
                d2:=d2+1;
            until d1 le d2+1 or d2+d2+d3 ge r+2;
            d3:=d3+1;
        until d2 le d3 or d3+d3+d3 ge r+2;

    elif l eq 4 then

        d2:=2;
        d3:=2;
        d4:=2;    
        d_mgd:=[];
        repeat
            d3:=d4;
            cf3:=Coefficient(G,t[4],d4);
            repeat
                d2:=d3;
                cf2:=Coefficient(cf3,t[3],d3);
                repeat 
                    isNegative:=false;
                    d1:=d2;
                    cf1:=Coefficient(cf2,t[2],d2);
                    repeat
                        if RationalField()! Coefficient(cf1,t[1],d1) le 1 then
                            d_mgd:=d_mgd cat [[d1,d2,d3,d4]];
                            isNegative:=true;
                        end if;
                        d1:=d1+1;
                    until isNegative eq true or d1+d2+d3+d4 ge r+2;
                    d2:=d2+1;
                until d1 le d2+1 or d2+d2+d3+d4 ge r+2;
                d3:=d3+1;
            until d2 le d3 or d3+d3+d3+d4 ge r+2;
            d4:=d4+1;
        until d3 le d4 or d4+d4+d4+d4 ge r+2;

    elif l eq 5 then

        d2:=2;
        d3:=2;
        d4:=2;
        d5:=2;    
        d_mgd:=[];
        repeat
            d4:=d5;
            cf4:=Coefficient(G,t[5],d5);
            repeat
                d3:=d4;
                cf3:=Coefficient(cf4,t[4],d4);
                repeat
                    d2:=d3;
                    cf2:=Coefficient(cf3,t[3],d3);
                    repeat 
                        isNegative:=false;
                        d1:=d2;
                        cf1:=Coefficient(cf2,t[2],d2);
                        repeat
                            if RationalField()! Coefficient(cf1,t[1],d1) le 1 then
                                d_mgd:=d_mgd cat [[d1,d2,d3,d4,d5]];
                                isNegative:=true;
                            end if;
                            d1:=d1+1;
                        until isNegative eq true or d1+d2+d3+d4+d5 ge r+2;
                        d2:=d2+1;
                    until d1 le d2+1 or d2+d2+d3+d4+d5 ge r+2;
                    d3:=d3+1;
                until d2 le d3 or d3+d3+d3+d4+d5 ge r+2;
                d4:=d4+1;
            until d3 le d4 or d4+d4+d4+d4+d5 ge r+2;
            d5:=d5+1;
        until d4 le d5 or d5+d5+d5+d5+d5 ge r+2;
    else
        d_mgd:=[];
    end if;
    
    return d_mgd;
end function;


RM := function(q,v,o,l,ll)

	n:=v+o;
    com:=Log(2,q^(l*v));
    d_opt:=[];
    n_opt:=0;

    for i in [0..o-1] do
        nn:=n-i;
        D:=RM_degree(2*o,nn,v+1,v,o,ll);
        for d in D do
            A:=Log(2,3*(v+1)^2*Binomial(nn,v)^2*&*[Binomial(v+d[i],d[i]): i in [1..ll]]^2);
            if A lt com then
                com := A;
                d_opt:=d;
                n_opt:=nn;
            end if;
        end for;
    end for;
	return com+Log(2, (2 * Log(2,q^l)^2) + Log(2,q^l)), n_opt, d_opt; 
end function;


q:=16;
v:=37;
o:=17;
l:=2;
ll:=2; //1=<ll=<l

v lt 2*o*ll; //condition for l'
RM(q,v,o,l,ll);
