from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary
#smooth example 2
_.<a,b> = QQ[]
f = a^6 + 1 
P = b^2 - f + a * b

q1 = [(1,j) for j in P(a=1).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q2 = [(2,j) for j in P(a=2).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q3 = [(3,j) for j in P(a=3).polynomial(b).roots(ring = QQbar, multiplicities = False)]
q4 = [(4,j) for j in P(a=4).polynomial(b).roots(ring = QQbar, multiplicities = False)]

D = [q1[0], q1[1]]#, q2[0], q2[1], q3[0], q3[1], q4[0], q4[1]]
E = []

HS = MHS.MixedHodgeStructure(P,D,E)

HS.period_matrix()
