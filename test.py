def factorise(f, n):
    var('q,t')
    SymmetricFunctions(QQ).s()
    supp = f.support()
    suppbis = f.support()
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for a,b in supp:
            if b == mu :
                result[mu] += [a]
    result2 = [(mu,sum(s(nu) for nu in result[mu])) for mu in result.keys()]
    for a,b in result2:
        #print a, latex(b)
        res += [[a,b.expand(1, 'q')]]
    return res
