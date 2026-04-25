from sage.hodge_theory import MHS

_.<a,b> = QQ[]

#triple node
P = b^3 - a^2 * b + a^4

E = [(0,0)]

HS = MHS.MixedHodgeStructure(P, D = E)

HS.period_matrix()
