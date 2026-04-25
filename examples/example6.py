from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary
#high genus example
#smooth example 2
_.<a,b> = QQ[]
f = a^6 + 1 
P = b^4 - f 

q1 = [(1,j) for j in P(a=1).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q2 = [(2,j) for j in P(a=2).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q3 = [(3,j) for j in P(a=3).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q4 = [(4,j) for j in P(a=4).polynomial(b).roots(ring = QQbar, multiplicities = False)]


HS = MHS.MixedHodgeStructure(P)

HS.homology()
HS._zero_res_basis()

HS.period_matrix()
