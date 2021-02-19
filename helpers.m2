slice= (lst, lens) -> (
    srt:= 0;
    fin:= -1;
    for i from 0 to (#lens-1) list(
	srt= fin + 1;
	fin= fin + lens#i;
	take(lst, {srt,fin})
	)
    )



comb= (idxs,varis) -> (
    name= value((separate("_", toString varis#0))#0);
    H=hashTable(apply(pairs name, reverse));
    product apply(varis, i -> i^(number(idxs, n -> n==H#i)))
    )

getTable= var -> (value first separate("_",toString var))
