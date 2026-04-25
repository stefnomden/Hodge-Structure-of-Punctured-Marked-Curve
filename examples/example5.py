from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

#node orbit example
_.<a,b> = QQ[]
f = (a^2 - 2)^3 - (a^2 - 2)^2
P = b^2 - f

q1 = (0, QQbar(sqrt(f(a=0))))
q2 = (QQbar(sqrt(2)), 0)
q2bar = (-QQbar(sqrt(2)), 0)

D = [q2,q2bar]
E = []


HS = MHS.MixedHodgeStructure(P,D,E)

HS.period_matrix()
