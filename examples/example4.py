#node example
_.<a,b> = QQ[]
f = a^3 + a^2
P = b^2 - f

q1 = (0,0)
q2 = (1,QQbar(sqrt(2)))

D = [q1,q2]
E = []

HS = MHS.MixedHodgeStructure(P,D,E)
HS._res_at_D_forms()

HS.period_matrix()
