from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

#cusp example
_.<a,b> = QQ[]
f = a^3
P = b^2 - f

q1 = (0,0)
q2 = (1,1)

D = [q1,q2]
E = []

HS = MHS.MixedHodgeStructure(P,D,E)
HS.period_matrix()
