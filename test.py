def factorise(f, n):
    SymmetricFunctions(QQ).s()
    supp = f.support()
    suppbis = f.support()
    result = {}
    for mu in Partitions(n):
        result[mu] = []
        for a,b in supp:
            if b == mu :
                result[mu] += [a]
    result2 = [(mu,sum(s(nu) for nu in result[mu])) for mu in result.keys()]
    for a,b in result2:
        print a, latex(b)
