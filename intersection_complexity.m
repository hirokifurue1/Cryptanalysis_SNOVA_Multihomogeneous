
//output possible solving multi-degrees
intersection_degree := function(n,o,l)

    R:=LazyPowerSeriesRing(RationalField(),l);

    G:=&*([&*[(1-R.i*R.j)^(8*o): j in [i+1..l]]: i in [1..l-1]] cat [1])
        *&*[(1-R.i*R.i)^(4*o-2): i in [1..l]]
        *&*[(1-R.i)^(-n): i in [1..l]];

    if l eq 1 then

        d1:=2;    
        d_mgd:=[];
        isNegative:=false;
        repeat
            if RationalField()! Coefficient(G,d1) le 1 then
                d_mgd:=[[d1]];
                isNegative:=true;
            end if;
            d1:=d1+1;
        until isNegative eq true or d1 ge n+1;

    elif l eq 2 then

        d2:=2;    
        d_mgd:=[];
        repeat 
            isNegative:=false;
            d1:=d2;
            repeat
                if RationalField()! Coefficient(G,[d1,d2]) le 1 then
                    d_mgd:=d_mgd cat [[d1,d2]];
                    isNegative:=true;
                end if;
                d1:=d1+1;
            until isNegative eq true or d1 ge n+1;
            d2:=d2+1;
        until d1 le d2+1;

    elif l eq 3 then

        d2:=2;
        d3:=2;    
        d_mgd:=[];
        repeat
            d2:=d3;
            repeat 
                isNegative:=false;
                d1:=d2;
                d2;
                repeat
                    if RationalField()! Coefficient(G,[d1,d2,d3]) le 1 then
                        d_mgd:=d_mgd cat [[d1,d2,d3]];
                        [d1,d2,d3];
                        isNegative:=true;
                    end if;
                    d1:=d1+1;
                until isNegative eq true or d1 ge n+1;
                d2:=d2+1;
            until d1 le d2+1;
            d3:=d3+1;
        until d2 le d3;

    elif l eq 4 then

        d2:=2;
        d3:=2;
        d4:=2;    
        d_mgd:=[];
        repeat
            d3:=d4;
            repeat
                d2:=d3;
                repeat 
                    isNegative:=false;
                    d1:=d2;
                    d1;
                    repeat
                        if RationalField()! Coefficient(G,[d1,d2,d3,d4]) le 1 then
                            d_mgd:=d_mgd cat [[d1,d2,d3,d4]];
                            [d1,d2,d3,d4];
                            isNegative:=true;
                        end if;
                        d1:=d1+1;
                    until isNegative eq true or d1 ge n+1; 
                    d2:=d2+1;
                until d1 le d2+1;
                d3:=d3+1;
            until d2 le d3;
            d4:=d4+1;
        until d3 le d4;

    elif l eq 5 then

        d2:=2;
        d3:=2;
        d4:=2;
        d5:=2;    
        d_mgd:=[];
        repeat
            d4:=d5;
            repeat
                d3:=d4;
                repeat
                    d2:=d3;
                    repeat 
                        isNegative:=false;
                        d1:=d2;
                        repeat
                            if RationalField()! Coefficient(G,[d1,d2,d3,d4,d5]) le 1 then
                                d_mgd:=d_mgd cat [[d1,d2,d3,d4,d5]];
                                [d1,d2,d3,d4,d5];
                                isNegative:=true;
                            end if;
                            d1:=d1+1;
                        until isNegative eq true or d1 ge n+1;
                        d2:=d2+1;
                    until d1 le d2+1;
                    d3:=d3+1;
                until d2 le d3;
                d4:=d4+1;
            until d3 le d4;
            d5:=d5+1;
        until d4 le d5;
    else
        d_mgd:=[];
    end if;
    
    return d_mgd;
end function;

intersection := function(q,v,o,l,ll)

	n:=v+o;
	com:=Log(2,q^(l*v));
    dd:=[];

	D:=intersection_degree(n,o,ll);

    for d in D do
	    A:=Log(2,q^(l*(v-2*o+1))*3*Binomial(n+1,2)*(&*[Binomial(n+d[i]-1,d[i]): i in [1..ll]])^2);
        if A lt com then
            com:=A;
            dd:=d;
        end if;
    end for;

	return com+Log(2, (2 * Log(2,q^l)^2) + Log(2,q^l)), dd; 

end function;

q:=16;
v:=37;
o:=17;
l:=2;
ll:=2; //1=<ll=<l

ll*(v+o) le 4*o*ll^2 - 2*ll; //condition for the number of variables and equations
intersection(q,v,o,l,ll);
