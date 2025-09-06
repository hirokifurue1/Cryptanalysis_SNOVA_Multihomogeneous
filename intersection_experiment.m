
////////////////////////parameter////////////////////////////////

q:=16;
v:=6;
o:=2;
l:=2;
//we consider the case of l=l'

d:=[2,2]; // solving degree

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

////////////////////////////intersection attack////////////////////////////////////

repeat
    W1:=&+[Random(exfield)*exPPsub[1][i]: i in [1..o]];
    W2:=&+[Random(exfield)*exPPsub[1][i]: i in [1..o]];
until IsInvertible(W1) and IsInvertible(W2);

W1Inv:=W1^(-1);
W2Inv:=W2^(-1);

qW1inv:=[Matrix([[W1Inv[i][j]^(q^(a-1)): j in [1..n]]: i in [1..n]]): a in [1..l]];
qW2inv:=[Matrix([[W2Inv[i][j]^(q^(a-1)): j in [1..n]]: i in [1..n]]): a in [1..l]];

PR<[x]>:=PolynomialRing(exfield,l*n,"glex");

X:=[];
for i in [1..l] do
    Append(~X,Vector([x[(i-1)*n+j]: j in [1..n]]));
end for;

//output degree d monomials in the I-th set of n variables
function MonomialsDegree(I, d)
    mons := [];
    exponents := MonomialsOfDegree(PolynomialRing(Rationals(), n), d);
    for e in exponents do
        exps := Exponents(e);
        mon := PR!1;
        for i in [1..n] do
            mon *:= X[I][i]^exps[i];
        end for;
        Append(~mons, mon);
    end for;
    return mons;
end function;

equation:=[];

for i in [1..l] do
    for j in [1..l] do
        //equation (10)
        equ:=[(X[i]*RMatrixSpace(PR,n,n)!(Transpose(qW1inv[i])*exPPsub[(i-1)*l+j][a]*qW1inv[j])*Transpose(Matrix(X[j])))[1]: a in [1..o]]
            cat [(X[i]*RMatrixSpace(PR,n,n)!(Transpose(qW1inv[i])*exPPsub[(i-1)*l+j][a]*qW2inv[j])*Transpose(Matrix(X[j])))[1]: a in [1..o]]
            cat [(X[i]*RMatrixSpace(PR,n,n)!(Transpose(qW2inv[i])*exPPsub[(i-1)*l+j][a]*qW1inv[j])*Transpose(Matrix(X[j])))[1]: a in [1..o]]
            cat [(X[i]*RMatrixSpace(PR,n,n)!(Transpose(qW2inv[i])*exPPsub[(i-1)*l+j][a]*qW2inv[j])*Transpose(Matrix(X[j])))[1]: a in [1..o]];

        //generate polynommials with multi-degree d by multiplying some monomials
        dd:=d;
        dd[i]:=dd[i]-1;
        dd[j]:=dd[j]-1;
        if dd[i] ge 0 and dd[j] ge 0 then
            mon:=MonomialsDegree(1,dd[1]);
            for a in [2..l] do
                mon:=&cat[[b*c: b in mon]: c in MonomialsDegree(a,dd[a])];
            end for;
            equation:=equation cat &cat[[mon[a]*equ[b]: a in [1..#mon]]: b in [1..#equ]];
        end if;
    end for;
end for;


//////////////////////////Macaulay matrix////////////////////////////////////////////////

monomial:=MonomialsDegree(1,d[1]);
for a in [2..l] do
    monomial:=&cat[[b*c: b in monomial]: c in MonomialsDegree(a,d[a])];
end for;

Mac:=Matrix(exfield,[[MonomialCoefficient(equation[i],j): j in monomial]: i in [1..#equation]]);

print("exp_NumberOfColumns");
NumberOfColumns(Mac);
print("Rank(Mac)=");
Rank(Mac);


//////////////////////////theoretical valuer///////////////////////////////////

R:=LazyPowerSeriesRing(RationalField(),l);

G:=&*([&*[(1-R.i*R.j)^(8*o): j in [i+1..l]]: i in [1..l-1]] cat [1])
    *&*[(1-R.i*R.i)^(4*o-2): i in [1..l]]
    *&*[(1-R.i)^(-(n)): i in [1..l]];

print("theo_NumberOfColumns");
&*[Binomial(n+d[i]-1,d[i]): i in [1..l]];
print("estimated rank");
&*[Binomial(n+d[i]-1,d[i]): i in [1..l]] - Max(Coefficient(G,d),0);
