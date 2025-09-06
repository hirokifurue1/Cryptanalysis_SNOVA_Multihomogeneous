
////////////////////////parameter////////////////////////////////

q:=16;
v:=3;
o:=1;
l:=2;
//we consider the case of l=l'

nn:=v+o; //the number of column used in support minors
d:=[1,1]; // solving degree |d| < v+2

// v < 2*l*o

/////////////////////////////////////////////////////////////

field:=GF(q);
n:=v+o;
gen:=PrimitiveElement(field);

PZ<x>:=PolynomialRing(field);

//choose an irreducible polynomial f to construct the extension filed in the case of q=16 case
if l eq 2 then
    f:=PZ! (x^2 + x + gen^3);
    S:=Matrix(field,[[gen^3,gen^10],[gen^10,gen^5]]);
elif l eq 3 then
    f:=PZ! (x^3 + x + gen^7);
    S:=Matrix(field,[[gen^3,gen^10,gen^5],[gen^10,gen^5,gen^8],[gen^5,gen^8,gen^2]]);
elif l eq 4 then
    f:=PZ! (x^4 + x^2 + gen * x + gen^2);
    S:=Matrix(field,[[gen^3,gen^10,gen^5,gen^8],[gen^10,gen^5,gen^8,gen^2],[gen^5,gen^8,gen^2,gen^4],[gen^8,gen^2,gen^4,gen]]);
elif l eq 5 then
    f:=PZ! (x^5 + x + gen^3);
    S:=Matrix(field,[[gen^3,gen^10,gen^5,gen^8,gen^2],[gen^10,gen^5,gen^8,gen^2,gen^4],[gen^5,gen^8,gen^2,gen^4,gen],[gen^8,gen^2,gen^4,gen,gen^0],[gen^2,gen^4,gen,gen^0,gen^15]]);
end if;
exfield := quo< PZ | f>;

////////////////////////key generation/////////////////////////////////

T0:=[VerticalJoin(HorizontalJoin(IdentityMatrix(field,v),RandomMatrix(field,v,o)),HorizontalJoin(ZeroMatrix(field,o,v),IdentityMatrix(field,o)))]
    cat [VerticalJoin(HorizontalJoin(ZeroMatrix(field,v,v),RandomMatrix(field,v,o)),HorizontalJoin(ZeroMatrix(field,o,v),ZeroMatrix(field,o))): i in [2..l]];
TT:=VerticalJoin([HorizontalJoin([&+[T0[k][i][j]*S^(k-1): k in [1..l]]: j in [1..n]]): i in [1..n]]);

FF:=[VerticalJoin(HorizontalJoin(RandomMatrix(field,l*v,l*v),RandomMatrix(field,l*v,l*o)),HorizontalJoin(RandomMatrix(field,l*o,l*v),ZeroMatrix(field,l*o,l*o))): i in [1..o]];

PP:=[Transpose(TT)*FF[i]*TT : i in [1..o]];

///////////////////////transformation into extension field in Section 4///////////////

ll:=Basis(Eigenspace(RMatrixSpace(exfield,l,l)! S, Random(Eigenvalues(RMatrixSpace(exfield,l,l)! S))[1]))[1];

L1:=Transpose(Matrix([[ll[i]^(q^(j-1)): i in [1..l]]: j in [1..l]]));
L:=DiagonalJoin([L1: i in [1..n]]);

U:=Transpose(PermutationMatrix(exfield,&cat[[i*l+j: i in [0..n-1]]: j in [1..l]]));

LU:=L*U;

exPP:=[Transpose(LU)*RMatrixSpace(exfield,n*l,n*l)!PP[i]*LU: i in [1..o]];

exPPsub:=[];
for i in [1..l] do
    for j in [1..l] do
        Append(~exPPsub,[Submatrix(exPP[a],(i-1)*n+1,(j-1)*n+1,n,n): a in [1..o]]);
    end for;
end for;

////////////////////////////rectangular MinRank////////////////////////////////////

//applying the rectangular transformation 
RM:=[];

for a in [1..l] do
    Append(~RM,[(Matrix([Transpose(exPPsub[a][j])[i]: j in [1..o]])):i in [1..n]]);
    Append(~RM,[(Matrix([(exPPsub[(a-1)*l+1][j])[i]: j in [1..o]])):i in [1..n]]);
end for;


PR<[x]>:=PolynomialRing(exfield,l*(v+1),"glex");
PR1<[y]>:=PolynomialRing(PR,Binomial(nn,v),"glex");

X:=[];
for i in [1..l] do
    Append(~X,Vector([PR1! x[(i-1)*(v+1)+j]: j in [1..v+1]] cat [PR1! 0: j in [1..o-1]]));
end for;

//output degree d monomials in the I-th set of n variables
function MonomialsDegree(I, d)
    mons := [];
    exponents := MonomialsOfDegree(PolynomialRing(Rationals(), v+1), d);
    for e in exponents do
        exps := Exponents(e);
        mon := PR!1;
        for i in [1..v+1] do
            mon *:= X[I][i]^exps[i];
        end for;
        Append(~mons, mon);
    end for;
    return mons;
end function;

JJ:=Setseq(Subsets({1..nn},v));

function Ind_y(J,JJ)
	i:=0;
	repeat
		i:=i+1;
	until J eq JJ[i];
	return i;
end function;

equation:=[];

for i in [1..l] do

    //generate support minor poly
    SM1:=&+[X[i][j]*RMatrixSpace(PR1,o,n)!RM[2*i-1][j]:j in [1..v+1]];
    SM2:=&+[X[i][j]*RMatrixSpace(PR1,o,n)!RM[2*i][j]:j in [1..v+1]];

    equ:=&cat[[&+[SM1[a][j] * y[Ind_y(J diff {j},JJ)] : j in J]: J in Subsets({1..nn},v+1)]:a in [1..o]]
        cat &cat[[&+[SM2[a][j] * y[Ind_y(J diff {j},JJ)] : j in J]: J in Subsets({1..nn},v+1)]:a in [1..o]];
    
    //generate polynommials with multi-degree d by multiplying some monomials
    dd:=d;
    dd[i]:=dd[i]-1;
    if dd[i] ge 0 then
        mon:=MonomialsDegree(1,dd[1]);
        for a in [2..l] do
            mon:=&cat[[b*c: b in mon]: c in MonomialsDegree(a,dd[a])];
        end for;
        equation:=equation cat &cat[[PR1! mon[a]*equ[b]: a in [1..#mon]]: b in [1..#equ]];
    end if;
end for;


//////////////////////////Macaulay matrix////////////////////////////////////////////////

monomial:=MonomialsDegree(1,d[1]);
for a in [2..l] do
    monomial:=&cat[[b*c: b in monomial]: c in MonomialsDegree(a,d[a])];
end for;

Mac:=ZeroMatrix(exfield,#equation,0);

for i in [1..#y] do
    i;
    Macx:=[];
    for j in [1..#equation] do
        coef_y:=MonomialCoefficient(equation[j],y[i]);
        Append(~Macx,[MonomialCoefficient(coef_y,PR!ii): ii in monomial]);
    end for;
    Mac:=HorizontalJoin(Mac,Matrix(Macx));
end for;


print("exp_NumberOfColumns");
NumberOfColumns(Mac);
print("Rank(Mac)=");
Rank(Mac);


//////////////////////////theoretical valuer///////////////////////////////////

PZ<[t]>:=PolynomialRing(RationalField(),l);

A:=Set(CartesianProduct([{0..v+1}: i in [1..l]])) diff {<0: i in [1..l]>};

G:=Binomial(n,v);
for dd in A do
    if &+[dd[i]: i in [1..l]] le v+1 then
        mon:=Binomial(n,v) * &*[Binomial(v+dd[i],dd[i]): i in [1..l]];

        Ad:=Set(CartesianProduct([{0..dd[i]}: i in [1..l]])) diff {<0: i in [1..l]>};

        equ:=&+[(-1)^(&+[b[i]: i in [1..l]]+1)
            *&*[Binomial(2*o+b[i]-1,b[i]): i in [1..l]]
            *Binomial(n,v+&+[b[i]: i in [1..l]])
            *&*[Binomial(v+dd[i]-b[i],dd[i]-b[i]):i in [1..l]]
            : b in Ad];

        G:=G+&*[t[i]^dd[i]:i in [1..l]]*(mon-equ);
    end if;
end for;

for i in [1..l] do
    G:=Coefficient(G,t[i],d[i]);
end for;

print("theo_NumberOfColumns");
&*[Binomial(v+d[i],d[i]): i in [1..l]]*Binomial(nn,v);

print("estimated rank");
&*[Binomial(v+d[i],d[i]): i in [1..l]]*Binomial(nn,v) - Max(RationalField()! G,0);
