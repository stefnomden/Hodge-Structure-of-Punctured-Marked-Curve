from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.matrix.constructor import matrix
from sage.arith.functions import lcm
from sage.hodge_theory import auxiliary
from sage.categories.homset import Hom
from sage.rings.qqbar import AlgebraicField
from sage.rings.rational_field import RationalField
from sage.rings.qqbar import number_field_elements_from_algebraics
from sage.rings.integer_ring import IntegerRing
from sage.modules.free_module_element import vector
from sage.symbolic.constants import I
from sage.rings.complex_mpfr import ComplexField
from sage.rings.real_mpfr import RealField
from sage.all import arg, log, factorial, ceil, prod, falling_factorial, pi
from sage.schemes.riemann_surfaces.riemann_surface import RiemannSurface, ConvergenceError
from sage.rings.complex_arb import ComplexBallField
from sage.rings.real_arb import RealBallField

from itertools import product



def voronoi(pts, n = 6):

    from sage.geometry.voronoi_diagram import VoronoiDiagram

    if len(pts) == 1: 
        smallest_dist = 1
    else:
        smallest_dist = min([
            AlgebraicField()(abs(alpha - beta)) for alpha in pts for beta in pts 
            if alpha != beta 
        ])


    prec = int(-RealField()(log(smallest_dist, 2))) + 53

    C = ComplexField(prec = prec)

    centre = sum(pts)/len(pts)
    radius = 2 * max([abs(centre - z) for z in pts]) if len(pts) != 1 else 1
    z = AlgebraicField().zeta(n)
    circle_points = [C(centre + radius * z ** i) for i in range(6)]

    return VoronoiDiagram([C(v) for v in pts] + circle_points)


class MixedHodgeStructure:

    def __init__(self, P, D, E, prec = 53):

        self._prec = prec
        self._P = P

        self._D_infinite = [a[:2] for a in D if (len(a) == 3 and a[-1] == 0)]

        self._D = (
            [(AlgebraicField()(a[0]), AlgebraicField()(a[1])) for a in D if len(a) == 2] + 
            [(AlgebraicField()(a[0]/a[-1]), AlgebraicField()(a[1]/a[-1])) for a in D if len(a) == 3 and a[-1] != 0]
        )
        
        
        self._E = [(AlgebraicField()(a), AlgebraicField()(b)) for a,b in E]
        if len(self._E) != 0:
            self._E_empty = False
        else: 
            self._E_empty = True

        self._E_as_index = []
        for a,b in E: 
            lifts = self.lift_pt(a)
            index = min(range(len(lifts)), key = lambda i : (lifts[i] - b).norm())
            self._E_as_index.append((a,index))


        numbers = self._check_singularities()

        self._d = P.degree(P.parent().gens()[1])
        self._Field = P.parent().base_ring() #should probably do this a little more careful: what if P is defined over QQbar, then in that case we would like to take a number field

        #Function Field over the base field k (=self._Field)
        K = FunctionField(self._Field, names = 'x')
        self._rational_ff = K
        x = K.gen()
        Y = PolynomialRing(K, names = 'Y').gen()
        self._function_field = K.extension(P(x,Y), names = 'y')
        self._y, self._x = self._function_field.gen(), self._rational_ff.gen()
        self._dx = self._function_field(self._x).differential()
        self._genus = self._function_field.genus()
        self._OC = self._function_field.maximal_order()
        self._OCoo = self._function_field.maximal_order_infinite()


        #smallest number field over which D is defined (along with embedding)
        self._abs_field, els, _ = number_field_elements_from_algebraics(
            [d[0] for d in self._D] + [d[1] for d in self._D] + 
            [d[0] for d in self._D_infinite] + [d[1] for d in self._D_infinite] +
            numbers + [AlgebraicField()(alpha) for alpha in self._Field.gens()],
            minimal = True,
            embedded = True,
            name = 'c'
        ) 

        self._D_abs = [(self._abs_field(els[i]), self._abs_field(els[i + len(self._D)])) for i in range(len(self._D))]
        self._D_abs_infinite = [(els[2 * len(self._D) + i], els[2 * len(self._D) + i + len(self._D_infinite)]) for i in range(len(self._D_infinite))]


        if self._abs_field.coerce_map_from(self._Field) == None:
            psi = Hom(self._Field, self._abs_field)([alpha for alpha in els[-len(self._Field.gens()):]])
            self._abs_field.register_coercion(psi)


        #we would like to use .extension_constant_field but this returns something which does not end up being that useful
        #namely, the action of the constant field you are extending does not work on this thing. 
        #self._function_field_D = self._function_field.extension_constant_field(self._abs_field)
        K = FunctionField(self._abs_field, names = 'x')
        Y = PolynomialRing(K,names = 'Y').gen()
        self._function_field_D = K.extension(P(x,Y), names = 'y')
        self._dx_D = self._function_field_D(self._x).differential()

        K = FunctionField(AlgebraicField(), names = 'x')
        Y = PolynomialRing(K,names = 'Y').gen()
        self._function_field_Qbar = K.extension(P(x,Y), names = 'y')


        #here we define the places corresponding to E. we do this over QQbar for now but this can be done more generally
        if not self._E_empty: 
            OCoo = self._function_field_Qbar.maximal_order()
            x,y = OCoo(self._x), OCoo(self._y)
            places_with_point = [(e,p) for e in self._E for p in OCoo.ideal(x - e[0], y - e[1]).divisor().support()]
            self._E_places = [p for _,p in places_with_point]
            self._E_unzipped = [e for e,_ in places_with_point] 
            self._E_dict = {p : i for i,p in enumerate(self._E_places)}


        C = RiemannSurface(self._P, differentials = [], prec = self._prec)
        self._C = C 

    def __repr__(self):


        if (self._D and not self._E_empty):
            s_D = '\nwith punctures         D = {}'.format(self._D)
            s_E = '\nand with marked points E = {}'.format(self._E) 
        elif self._D:
            s_D = '\nwith punctures D = {}'.format(self._D)
            s_E = ''
        elif not self._E_empty:
            s_D = ''
            s_E = '\nwith marked points E = {}'.format(self._E) 
        else: 
            s_D = ''
            s_E = ''


        return 'Mixed Hodge structure associated to the curve C: {} = 0'.format(self._P) + s_D + s_E

    def genus(self):
        return self._genus

    def _get_annihilator(self, g):

        F = g.parent().constant_base_field()

        derivatives = []
        r = 0
        while matrix(derivatives).rank() == r:
            derivatives.append((g.higher_derivative(r)*factorial(r)).list())
            r += 1
        v = matrix(derivatives).kernel().basis()[0]

        from ore_algebra import OreAlgebra

        #right now we take polynomial ring over QQ but we should really take general fields
        pols = PolynomialRing(F, names = 't')
        t = pols.gen()
        Dt = OreAlgebra(pols,'Dt').gen()

        v *= lcm(f.denominator() for f in v)

        return sum(f.element().numerator()(t) * Dt ** i for i,f in enumerate(v))


    def _get_initial_data(self, g, p, annihilator = None, local_basis = False, with_places = False):
        #input: element of the function field g, an affine point/place p 
        #output: the annihilator L of g and the initial datas [[c_0, ... ,c_d], ... ] such that 
        #g is the solution to L * g given any element of the initial data.
        #note that when L is non-singular at x(p), then there is only one initial data


        #NOTE: we are doing a lot over Qbar in this function, it could be faster if we work over the field K(I)
        #where K is the field over which g is defined and I is the imaginary unit.
        #this should not be too much work but it could be

        #note to future stef: we (you and i) should make sure that if we do this, a has to be defined over Q(I)
        #which is not the case as it is now I think. 
        '''

        K = g.parent().constant_base_field()
        t = PolynomialRing(K, names = 't').gen()
        if not (t ** 2 + 1).roots():
            K_I = K.extension(t ** 2 + 1, names = 'I')

            if AlgebraicField().coerce_map_from(K_I) == None:

                AlgebraicField().register_coercion(
                    Hom(K_I, AlgebraicField())([AlgebraicField()(I)])
                )
            temp = FunctionField(K_I, names = 'x')
            x_temp = temp.gen()
            Y = PolynomialRing(temp, names = 'Y').gen()
            kC_I = temp.extension(self._P(x_temp,Y), names = 'y')
        
        else: 
            kC_I = g.parent()

        print(kC.coerce_map_from(kC_I))
        '''

        kC = self._function_field_Qbar

        x = self._x
        a,b = p

        if annihilator == None: 
            L = self._get_annihilator(g) 
        else: 
            L = annihilator
        t = L.base_ring().gen()
        rho_values = [RationalField()(z.degree(t)) for z in L.local_basis_monomials(a)]
        L_i = lambda f,i : (kC(x) - a) * f.derivative() - rho_values[i] * f

        def S_n(f,n): 
            for i in range(n):
                f = L_i(f,i)
            return f

        def eval_special(g):
            """
            s = PolynomialRing(AlgebraicField(), names = 's').gen()

            numerator = sum(
                sum(c * a**j for j,c in enumerate(f.element().numerator().list())) * 
                s ** i for i,f in enumerate(g.element().numerator().list())
            )
            denominator = sum(
                c * a ** j for j,c in enumerate(g.element().denominator().list())
            )
        
            if denominator != 0: 
                return [numerator(b)/denominator]
            """
            try: 
                val = self.eval(g,p)
            except ValueError:
                #if the denominator is equal to 0 then we have a 0/0 situation on our hand and we 
                #evaluate at every place. 
                p_place = kC.maximal_order().ideal(kC(self._x) - a, kC(self._y) - b).divisor().support()
                return [(g.evaluate(p), p) for p in p_place]
            else: 
                return [(val, None)]



        initial_values = []
        corr_places = [] 
            
        for n,rho in enumerate(rho_values): 
            Lambda = prod(rho - rho_values[i] for i in range(n))
            k = max(0, ceil(rho))
            h_n = S_n(g, n)

            u,v = abs((rho - k).numerator()), abs((rho - k).denominator())
            f_d_rho = falling_factorial(rho,k)

            #this part takes a while since everything is defined over Qbar which tends to be slow
            #here c_n_v is an array: at a singular point, we may get the issue that there are two places above this point
            #the issue then becomes that the evaluation may not be well-defined, thus the evaluation is possibly multivalued.
            #each of these values corresponds to a different path g can take.
            c_n_v = eval_special(
                ((kC(x) - a) ** u) * ((~(f_d_rho * Lambda) * factorial(k) * h_n.higher_derivative(k)) ** v)
            )

            temp = []
            for c, pl in c_n_v:

                z = AlgebraicField().zeta(v)
                c_n = AlgebraicField()(c ** (1/v))
                temp.extend([(c_n * z ** i, pl) for i in range(v)])

            initial_values.append(temp)
            
        #book keeping for initial values, we have all the possibilities for every coefficient of the 
        #monomial basis, but we want to package initial conditions as ([c_0, c_1, .., c_n], place) not as
        #[[possible c_0,place], [possible c_1,place], .., [possible c_n,place]]    
        output = [list(tup) for tup in product(*initial_values)]
        output = [tup for tup in output if len(set(c[1] for c in tup)) <= 1]
        output = [([a[0] for a in tup], tup[0][1]) if tup else [] for tup in output]

        if not with_places:
            output = [tup[0] if tup else [] for tup in output]

        self._test = initial_values

        if local_basis:
            return L, output, rho_values
        else:
            return L, output 



    def _check_singularities(self):

        from sage.arith.misc import gcd

        a,b = self._P.parent().gens()

        P_a = self._P.derivative(a)
        P_b = self._P.derivative(b)

        r1 = self._P.resultant(P_a, variable = b)
        r2 = self._P.resultant(P_b, variable = b)

        t = PolynomialRing(AlgebraicField(), name = 't').gen()

        x_coords = gcd(r1, r2).polynomial(a).roots(ring = AlgebraicField(), multiplicities = False)

        singularities = [
            (x, y) for x in x_coords 
            for y in self._P(x,t).roots(ring = AlgebraicField(), multiplicities = False)
            if (self._P(x,y) == 0 and P_a(0,0) == 0 and P_b(0,0) == 0)
            ]
        
        self._singularities = singularities

        self._D_sing = [d for d in self._D if d in singularities]
        self._E_sing = [e for e in self._E if e in singularities]

        numbers = [n for x,y in self._D_sing for n in auxiliary.numbers_generating_residue(self._P(a + x, b + y))]

        return numbers

    def eval(self, g, p, place = None):
        s = PolynomialRing(AlgebraicField(), names = 's').gen()
        a,b = p

        numerator = sum(
            sum(c * a**j for j,c in enumerate(f.element().numerator().list())) * 
            s ** i for i,f in enumerate(g.element().numerator().list())
        )
        denominator = sum(
            c * a ** j for j,c in enumerate(g.element().denominator().list())
        )

        if denominator != 0: 
            return numerator.subs(s = b)/denominator
        else: 
            if place == None: 
                raise ValueError('denominator is equal to 0')
            return g.evaluate(place)
            


    def _zero_res_basis(self):

        if hasattr(self, '_basis_zero_res'):
            return self._basis_zero_res

        def check_dim(forms, functions):
            #input: a set of rational 1-forms and a finite subset of kC
            #output: the dimension of <forms> modulo <dfunctions>
            if forms == []:
                return 0
            kC = forms[0].parent().base_ring()
            x = kC.base_ring().gen()
            dx = kC(x).differential()
            big_space = [f.derivative() for f in functions] + [omega/dx for omega in forms]
            polyring = kC(x).element().list()[0].numerator().parent() #fix this line lol
            D_x = lcm([polyring(lcm([a.denominator() for a in f.element().list()])) for f in big_space])
            big_space_cleared = [D_x * f for f in big_space]
            N = max( [max( [a.numerator().degree() for a in f.list()] ) for f in big_space_cleared] ) + 1

            to_be_matrix = []

            for f in big_space_cleared:
                row = []
                for a in f.list():
                    coefficients = a.numerator().list()
                    row.extend(coefficients + (N - len(coefficients)) * [0])
                to_be_matrix.append(row)
            A = matrix(to_be_matrix)

            #apply the equations dim(V cap W) = dim(V) + dim(W) - dim(V + W)
            #               and  dim(V/S) = dim(V) - dim(S)
            dim_of_sum = A.rank()
            dim_of_dLR = A[:len(functions)].rank()
            return dim_of_sum - dim_of_dLR


        if self._genus == 0:
            self._index = 1
            return []
        #right now the off_set is constant zero but we would like it to not be equal to the   
        #x coordinate of a point in E or a branch point
        off_set = self._Field(1/3)
        x,y = self._x, self._y
        places_above_zero = list(map(lambda L : L[0].place(), self._OC.ideal(x-off_set).factor()))
        places_above_infty = list(map(lambda L : L[0].place(), self._OCoo.ideal(1/x).factor()))
        divx = self._function_field(x).divisor_of_poles()
        div1_over_x = self._function_field(1/x).divisor_of_poles()
        divy = y.divisor_of_poles()
        canon_div_of_poles = divx + sum(divx.support())
        self._canon_div_of_poles = canon_div_of_poles

        index = 1
        functions = [y**i for i in range(1,self._d)]
        forms = [f*self._dx for f in functions]
        residues = []


        #calculate forms with residue 0 by calculating the kernel of the 'residue matrix'
        j = 0
        while len(residues) <= 2*self._genus or len(A.kernel().basis()) < 2*self._genus + 3:
            #the functions we generate only have poles above zero or infinity
            print(forms[j])
            import time
            start = time.time()
            residues.append([r for p in places_above_zero + places_above_infty for r in forms[j].residue(p).list()])
            print('time: {}'.format(time.time() - start))
            A = matrix(residues)
            #print(A.kernel().basis(),end = '\n\n')
            #generate more functions if we run out
            if j + 1 == len(functions): 
                functions.extend([y**i * (x - off_set)**(-index) for i in range(0,self._d)] + [y**i * (x-off_set)**(index) for i in range(0,self._d)])
                forms = [f*self._dx for f in functions]
                index += 1
            j += 1 

        zero_residue_forms = [sum([b*forms[i] for i,b in enumerate(v)]) for v in A.kernel().basis()]
        basis = []
        R = index * divx + (self._d - 1) * divy + index * div1_over_x + canon_div_of_poles
        self._R = R
        L_of_R = R.basis_function_space()
        self._L_of_R = L_of_R
        k = 0

        while len(basis) < 2*self._genus:
            #print('len(basis) = {}'.format(len(basis)))
            potential_new_basis = basis + [zero_residue_forms[k]]
            if check_dim(potential_new_basis,L_of_R) > len(basis):
                basis.append(zero_residue_forms[k])

            if k + 1 == len(zero_residue_forms) and len(basis) != 2*self._genus:
                extra_residues_to_compute = 2*self._genus - len(basis)
                for _ in range(extra_residues_to_compute):
                    if j + 1 == len(functions):
                        functions.extend([y**i * (x - off_set)**(-index) for i in range(0,self._d)] + [y**i * (x - off_set)**(index) for i in range(0,self._d)])
                        forms = [f*self._dx for f in functions]
                        index += 1
                    residues.append([r for p in places_above_zero + places_above_infty for r in forms[j].residue(p).list()])
                    j += 1
                A = matrix(residues)
                zero_residue_forms = [sum([b*forms[i] for i,b in enumerate(v)]) for v in A.kernel().basis()]
                basis = []
                R = index*divx + (self._d-1)*divy + index*div1_over_x + canon_div_of_poles
                L_of_R = R.basis_function_space()
                k = -1
            k += 1
        
        self._index = index
        self._basis_zero_res = basis

        return basis
    
    def _res_at_D_forms(self):

        if hasattr(self, '_res_at_D'):
            return self._res_at_D

        orbit = auxiliary.orbit_relative
        
        #Here we detect the orbits which contained in D. Note that we do this on the points on in the field K(c) = K(D) (for some c).
        #since the absolute field K(c) is relative to QQ (instead of K), we find the orbit over QQbar and collect the corresponding elements
        #in K(c). 
        checked = []
        orbits = []
        for p in self._D_abs: 
            if p in checked:
                continue
            p_orbit = [
                (x_coord, y_coord) for x_coord in orbit(p[0], self._abs_field, K = self._Field) 
                for y_coord in orbit(p[1], self._abs_field, K = self._Field)
            ]
            if len(p_orbit) != 1 and all(i in self._D_abs for i in p_orbit):
                checked.extend(p_orbit)
                orbits.append(p_orbit)

        self._orbits = orbits
        self._checked = checked

        D_non_orbs = [p for p in self._D_abs if p not in checked]


        kC = self._function_field_D
        x,y = kC(self._x), kC(self._y)
        OC = kC.maximal_order()

        self._OC_D = OC


        places = [OC.ideal(x - a, y - b).divisor() for (a,b) in D_non_orbs]

        #Find places for points at infinity
        if self._D_infinite:
            OCoo = kC.maximal_order_infinite()
            #this is supposed to be the coordinate vanishing at the point p at infinity (?)
            t = OCoo.basis()[1]
            inf_divisors = [
                OCoo.ideal(1/x, (t - p[1]/p[0] if p[0] != 0 else ~t - p[0]/p[1])).divisor()
                for p in self._D_abs_infinite
            ]
            places += inf_divisors

        places_support = [p for D in places for p in D.support()]

        orbit_places = [OC.ideal(x - a, y - b).divisor() for O in orbits for (a,b) in O]
        orbit_support = [p for D in orbit_places for p in D.support()]

        self._places = orbit_support + places_support
        self._divisors = orbit_places + places

        forms = []
        residue_matrix = []
        r = 0

        def check_add_forms(divisor, rowbuilder):
            nonlocal r 

            for omega in divisor.basis_differential_space():

                row = rowbuilder(omega)
                if matrix(residue_matrix + [row]).rank() > r:
                    forms.append(omega)
                    residue_matrix.append(row)
                    r += 1

        if len(orbit_places) != 0:
            divisor = -sum(orbit_places)
            def rowbuilder(omega):
                return (
                    [omega.residue(p) for p in orbit_support] + 
                    [0] * len(places_support)
                )
            check_add_forms(divisor, rowbuilder)

        if len(places) != 0 and len(orbit_places) != 0:
            divisor = -sum(orbit_places) - places[-1]
            def rowbuilder(omega):
                return (
                    [omega.residue(p) for p in orbit_support] + 
                    [0] * (len(places_support) - len(places[-1].support())) +
                    [omega.residue(p) for p in places[-1].support()]
                )
            check_add_forms(divisor, rowbuilder)

        if len(places) > 1:
            divisor = -sum(places)
            def rowbuilder(omega):
                return (
                    [0] * len(orbit_support) +
                    [omega.residue(p) for p in places_support]
                )
            check_add_forms(divisor, rowbuilder)

        self._residue_matrix = residue_matrix
        self._res_at_D = forms

        return forms
        
        
    def cohomology(self):

        from sage.rings.function_field.maps import (
            FunctionFieldLinearMap, FunctionFieldLinearMapSection
            )
        from sage.categories.cartesian_product import cartesian_product


        A = self._function_field_D.space_of_differentials()
        zero_residue = self._zero_res_basis()
        non_zer_residue = self._res_at_D_forms()


        if not self._E_empty:

            QE = AlgebraicField()**(len(self._E_places))
            H = cartesian_product([A,QE])
            self._H = H

            V = AlgebraicField()**(len(zero_residue) + len(non_zer_residue) + len(self._E_places) - 1)

        else: 
            V = AlgebraicField()**(len(zero_residue) + len(non_zer_residue))

        self._V = V


        #define maps from V to space of differentials
        def from_V(v):
            n = len(zero_residue)
            m = len(non_zer_residue)
            sigma = self._abs_field.convert_map_from(AlgebraicField())
            omega = sum(sigma(a) * w for a,w in zip(v[:n], zero_residue))
            eta = sum(sigma(a) * w for a,w in zip(v[n:n + m], non_zer_residue))
            if self._E_empty:
                return omega + eta
            w = vector([AlgebraicField()(a) for a in v[n + m:]] + [0])
            return H((omega, QE.zero())) + H((eta, QE.zero())) + H((A.zero(), QE(w)))


        #sadly these need to be computed again since here we work over k(D)(C) rather than k(C)
        poles_of_x = self._function_field_D(self._x).divisor_of_poles()
        poles_of_x_inv = self._function_field_D(self._x).divisor_of_zeros()
        poles_of_canon_div = poles_of_x + sum(poles_of_x.support())
        poles_of_y = self._function_field_D(self._y).divisor_of_poles()
        R = (
            self._index * poles_of_x +
            (self._d - 1) * poles_of_y + 
            self._index * poles_of_x_inv +
            poles_of_canon_div
        )


        def to_V(omega):

            if not self._E_empty:
                omega, vec = omega
        
            v = vector([omega.residue(p) for p in self._places[:-1]])

            residue_vector = v * matrix([row[:-1] for row in self._residue_matrix]).inverse()
        

            residue_part_of_omega = sum(a * w for a,w in zip(residue_vector, self._res_at_D_forms()))

            eta = omega - residue_part_of_omega
            if eta == self._function_field_D.space_of_differentials().zero():
                if self._E_empty:
                    return self._V( len(self._zero_res_basis()) * [0] + residue_vector.list())
                v = [i - vec[-1] for i in vec[:-1]]
                return self._V(len(self._zero_res_basis()) * [0] + residue_vector.list() + v)

            #the divisor of poles of eta and the divisor which is such that every element omega representing 
            #cohomology is such that div(omega) + R >= 0
            eta_div_of_poles = eta._f.divisor_of_poles() + poles_of_canon_div


            #R_tilde = max(R,(eta)_infty) 
            R_tilde = sum(max([div.dict().get(p,0) for div in [R,eta_div_of_poles]]) * p for p in (eta_div_of_poles + R).support())
            #lower the degree of every entry
            R_tilde = R_tilde - sum(R_tilde.support())

            if R_tilde == R: 
                L_R = self._L_of_R
            else: 
                L_R = R_tilde.basis_function_space()

            big_space = [omega._f for omega in self._zero_res_basis()] + [f.derivative() for f in L_R] + [eta._f]
            polyring = self._function_field_D.base_ring()._ring
            self._test = big_space
            self._polyring = polyring
            D_x = self._function_field_D(lcm([polyring(lcm([a.denominator() for a in f.element().list()])) for f in big_space]))
            big_space_cleared = [D_x * f for f in big_space]
            N = max([max([a.numerator().degree() for a in f.list()] ) for f in big_space_cleared] ) + 1

            to_be_matrix = []

            for f in big_space_cleared:
                row = []
                for a in f.list():
                    coefficients = a.numerator().list()
                    row.extend(coefficients + (N - len(coefficients)) * [0])
                to_be_matrix.append(row)
            
            A = matrix(to_be_matrix)

            relevant_vectors = [v for v in A.kernel().basis() if v[-1] != 0]

            v = relevant_vectors[0]

            f = self._function_field_D(-1/v[-1]) * sum(v[i+len(self._zero_res_basis())] * g for i,g in enumerate(L_R))

            coordinates = (-1/v[-1])*v[:len(self._zero_res_basis())]

            if self._E_empty:
                return V(coordinates.list() + residue_vector.list())
            

            f_eval_vector = [self._function_field_Qbar(f).evaluate(p) for p in self._E_places]
            v = [a - b for a,b in zip(vec, f_eval_vector)]
            v = [i - v[-1] for i in v[:-1]]

            return V(coordinates.list() + residue_vector.list() + v)

        self._test_map = to_V
        
        if not self._E_empty:
            lin_map_from_V = FunctionFieldLinearMap(Hom(V, H), from_V)
            lin_map_to_V = FunctionFieldLinearMapSection(Hom(H, V), to_V)
        else: 
            lin_map_from_V = FunctionFieldLinearMap(Hom(V, A), from_V)
            lin_map_to_V = FunctionFieldLinearMap(Hom(A, V), to_V)


        return V, lin_map_from_V, lin_map_to_V
        

    def cohomology_basis(self):

        if not hasattr(self, '_cohomology_basis'):
            V, f, _ = self.cohomology()
            self._cohomology_basis = [f(v) for v in V.basis()]
        
        return self._cohomology_basis
    
    def lift_pt(self, v):
        t = PolynomialRing(AlgebraicField(), names = 't').gen()
        return self._P(v, t).roots(ring = AlgebraicField(), multiplicities = False)


    def _set_plane_graph(self):

        t = PolynomialRing(AlgebraicField(), names = 't').gen()

        self.branch_points = self._P.discriminant(self._P.parent().gens()[1])(t,0).roots(multiplicities = False)

        self.branch_points_and_xD = self.branch_points + [x[0] for x in self._D if x[0] not in self.branch_points] 

        self._E_ramif = [e for e in self._E if e[0] in self.branch_points] 

        V = voronoi(self.branch_points_and_xD, n = 6)
        self._voronoi_graph = V
        
        relevant_points = V.points()[:len(self.branch_points_and_xD)]
        self._test_vals = relevant_points
        relevant_regions = [V.regions().get(p) for p in relevant_points]
        self._plane_verts = list(set([
            RationalField()(v[0]) + RationalField()(v[1]) * I 
            for R in relevant_regions for v in R.vertices()
            ]))
        
        self._plane_edges = []
        self._plane_loops = []

        for k,p in enumerate(relevant_points):
            local_centre = RationalField()(list(p)[0]) + RationalField()(list(p)[1]) * I
            local_vertices = [
                RationalField()(list(v)[0]) + RationalField()(list(v)[1]) * I
                for v in V.regions().get(p).vertices()
            ]    
            local_vertices.sort(key = lambda z : arg(local_centre - z))
            
            new_edges = list(zip(local_vertices, local_vertices[1:] + local_vertices[:1]))

            #if the unique branch point lying in this center is an x-coord of E then we would like to 
            #add this to the 'loop' since this will split the lifted loop into more than one loop. 
            if self.branch_points_and_xD[k] in [e[0] for e in self._E]:

                e = self.branch_points_and_xD[k] 
                self._plane_verts += [e]

                close_to_e = min(
                    local_vertices,
                    key = lambda z : abs(z - e)
                )

                new_edges += [(e, close_to_e)]


            self._plane_loops.append(new_edges)


            self._plane_edges.extend([
                e for e in new_edges if (e not in self._plane_edges and (e[1],e[0]) not in self._plane_edges)
                ])

        infinite_regions = [V.regions().get(p) for p in V.points()[len(self.branch_points_and_xD):]]
        outside_vertices = list(set([
            RationalField()(v[0]) + RationalField()(v[1]) * I
            for R in infinite_regions for v in R.vertices()
            ]))
        
        c = sum(outside_vertices)/len(outside_vertices)
        outside_vertices.sort(key = lambda z : arg(z - c))
        self._plane_loops.append(list(zip(outside_vertices, outside_vertices[1:] + outside_vertices[:1])))


        for e in self._E:
            if (e[0] not in self._plane_verts) and (e[0] not in self.branch_points):
            #if (e[0] not in self._plane_verts):
                close_to_e = min(
                    self._plane_verts,
                    key = lambda z : abs(z - e[0]) 
                    )
                self._plane_verts += [e[0]]
                self._plane_edges.append((e[0], close_to_e))
                
    def _set_upstairs_graph(self):

        self._upstairs_graph = []
        remaining_edges = []
        self._edge_dict = dict()

        self._giga_test = []

        counter = 1

        #here we lift every edge in the plane graph which does not have starting or ending 
        #vertex in x(E). To lift these paths we mainly use the version implemented by 
        #Nils Bruin (RiemannSurface package in Sage)
        for e in self._plane_edges:

            if not (e[0] in self.branch_points or e[1] in self.branch_points):

                ini_lifts = self.lift_pt(e[0])
                ter_lifts = self.lift_pt(e[1])


                try: 
                    temp = [(E[0], E[-1]) for E in zip(*[x[1] for x in self._C.homotopy_continuation(e)])]
                except ConvergenceError: 
                    C_high_prec = RiemannSurface(self._P, differentials = [], prec = 2 * self._prec)
                    temp = [(E[0], E[-1]) for E in zip(*[x[1] for x in C_high_prec.homotopy_continuation(e)])]

                self._giga_test += [temp]

                for a,b in temp: 
                    ini = (
                        e[0], ini_lifts.index(min(ini_lifts, key = lambda alpha : (a - alpha).norm()))
                    )
                    ter = (
                        e[1], ter_lifts.index(min(ter_lifts, key = lambda alpha : (b - alpha).norm()))
                    )
                    

                    self._upstairs_graph.append((ini,ter))
                    point = (AlgebraicField()(ini[0]), self.lift_pt(ini[0])[ini[1]])
                    if point in self._E:
                        #there will only be one element in self._E_unzipped equal to point since if there were multiple, 
                        #then this edge would not survive the first if clause. Hence asking for the index as below is fine.
                        self._edge_dict.update({(ini,ter) : self._E_places[self._E_unzipped.index(point)]})
            else: 
                remaining_edges.append(e)


            self._test_for_testing = self._upstairs_graph
            self.remaining_edges = remaining_edges
            self._test_edges = []

        for e in remaining_edges:
            
            ini_lifts = self.lift_pt(e[0])
            ter_lifts = self.lift_pt(e[1])

            for i, initial_pt in enumerate(ini_lifts):

                L, inits = self._get_initial_data(self._y, (e[0],initial_pt), with_places = True)
                corresponding_places = [ini[1] for ini in inits]
                inits = [ini[0] for ini in inits]
                sols = [L.numerical_solution(ini = ini, path = [e[0], e[1]]) for ini in inits]

                for j, terminal in enumerate(ter_lifts):

                    value_check = [0 in Ball - terminal for Ball in sols]

                    if any(value_check):
                        k = value_check.index(True)
                        ini = (e[0], i)
                        ter = (e[1], j)
                        self._upstairs_graph.append((ini, ter))
                        self._test_edges.append((ini,ter))

                        #the lifted edge here is going to connect to ini but spiritually (and mathematically) this edge corresponds 
                        #to the point in the normalization corresponding to this place. 
                        print('place:', corresponding_places[k])
                        if corresponding_places[k] != None: 
                            self._edge_dict.update({(ini,ter) : corresponding_places[k]}) 
                        else: 
                            self._edge_dict.update({(ini, ter) : self._E_places[self._E_unzipped.index((e[0],initial_pt))]})
                        

        self._upstairs_vertices = list(set(
            [e[0] for e in self._upstairs_graph] + 
            [e[1] for e in self._upstairs_graph]
        ))
                

    def homology_basis(self):
        #Note: returns a basis as Z-vectors rather than actual topological loops. 
        #these vectors mean something when taking into account the ordered basis self._upstairs_graph
        #where an elements of self._upstairs_graph is a tuple of points (a,b) on C which represents a lift of 
        #the straight path connecting (x(a), x(b)) on the plane. 


        if not hasattr(self, '_plane_verts'):
            self._set_plane_graph()
        if not hasattr(self, '_upstairs_graph'): 
            self._set_upstairs_graph()


        #first we find the cohomology of the lifted graph. the ZZ-bases for the vertices and edges are considerd
        #to be ordered. 
        A = matrix(
            [[0 if v in self._E_as_index else {e[0] : 1, e[1] : -1}.get(v,0) for v in self._upstairs_vertices] 
            for e in self._upstairs_graph]
        )
        graph_cohom = A.kernel().basis()
        #graph_cohom = [v for v in matrix(graph_cohom).LLL()]
        self._graph_cohom = graph_cohom

        K = []
        self._test_loops = []
        self._test_kernels = []

        for O in self._plane_loops:
            lifted_loop = [e for e in self._upstairs_graph if ((e[0][0], e[1][0]) in O or (e[1][0], e[0][0]) in O)]
            self._test_loops.append(lifted_loop)

            vert_temp = list(set(
                [e[0] for e in lifted_loop] + [e[1] for e in lifted_loop]
            ))

            A_O = matrix(
                [[{e[0] : 1, e[1] : -1}.get(v,0) for v in vert_temp] for e in lifted_loop]
            )

            self._test_kernels += [A_O.kernel().basis()]

            dicts = [{e : a for e,a in zip(lifted_loop, v)} for v in A_O.kernel().basis()]

            K.extend(
                [[D.get(e,0) for e in self._upstairs_graph] for D in dicts]
            )
        
        #K = [v for v in matrix(K).LLL() if v != 0]

        self._K_loops_ordered = [[{1 : e, -1 : (e[1],e[0])}.get(a) for e,a in zip(self._upstairs_graph,v) if a != 0] for v in K]
        self._lifted_loops = self._K_loops_ordered


        #here we remove the loops that lie around points in D from the kernel K. 
        to_be_removed = []

        for d in self._D:
            close_to_d = min(self._plane_verts, key = lambda z : abs(z - d[0]))
            path = [d[0], close_to_d]

            L,inits = self._get_initial_data(self._y, d)

            endpts = [L.numerical_solution(ini = ini, path = path) for ini in inits]
            lifts = self.lift_pt(close_to_d)
            indices = [lifts.index(min(lifts, key = lambda z : abs(z - a))) for a in endpts]

            verts = [(close_to_d, i) for i in indices]

            i,_ = min(enumerate(self._plane_loops),
                   key = lambda A : sum(abs(d[0] - v) for v in {e[0] for e in A[1]} | {e[1] for e in A[1]})/len(A[1])
            )
        
            d_lifted_loops = [
                [{1 : self._test_loops[i][j], -1 : (self._test_loops[i][j][1], self._test_loops[i][j][0])}.get(a)
                for j,a in enumerate(v) if a != 0] for v in self._test_kernels[i]
            ]  

            d_lifted_loops_verts = [list({e[0] for e in O} | {e[1] for e in O}) for O in d_lifted_loops] 

            indices_to_be_removed = []
            for v in verts:
                for k, vertices in enumerate(d_lifted_loops_verts):
                    if (v in vertices) and (k not in indices_to_be_removed):
                        indices_to_be_removed.append(k)

            for k in indices_to_be_removed:
                i = self._K_loops_ordered.index(d_lifted_loops[k])
                to_be_removed.append(i)
            


        loops_around_oo = self._K_loops_ordered[-len(self._test_kernels[-1]):]
        if len(loops_around_oo) == len(self._D_infinite):
            k = len(loops_around_oo)
            to_be_removed.extend(
                list(range(len(self._K_loops_ordered)))[-k:]
            )
        else: 
            for d in self._D_infinite:
                OC = self._function_field_D.maximal_order_infinite()
                t = OC.basis()[1]
                g = t - d[1]/d[0] if d[0] != 0 else ~t - d[0]/d[1]
                for loop in loops_around_oo:
                    winding = 0
                    
                    for start, end in loop: 
                        to_p = lambda a : (a[0], self.lift_pt(a[0])[a[1]]) 

                        en = ComplexBallField(20)(self.eval(g,to_p(end)))
                        st = ComplexBallField(20)(self.eval(g,to_p(start)))

                        winding += RealBallField(20)(arg(en/st)/(2 * pi()))

                    if 0 not in winding: 
                        i = self._K_loops_ordered.index(loop)
                        to_be_removed.append(i)


        K = [v for i,v in enumerate(K) if i not in to_be_removed]
        self.K = K

        vector_basis = []
        r = 0
        for v in graph_cohom:
            if matrix([v] + vector_basis + K).rank() - matrix(K).rank() > r:
                vector_basis.append(v)
                r += 1

        self._basis_homology = [v for v in matrix(vector_basis).LLL()]
        G = self._upstairs_graph
        self._basis_loops = [[G[i] if a == 1 else (G[i][1], G[i][0]) for i,a in enumerate(v) if a != 0] for v in self._basis_homology]
        
        return self._basis_homology


    def _integrate_edge(self, omega, e, eps = 1e-16):

        start, end = e

        if not self._E_empty:

            omega,v = omega

            #here we check what the orientation of e is w.r.t. how it occurs in self._upstairs_graph 
            #the boundary values will only contribute if one of the endpoints is a point in E, hence, we only 
            #have to check the E_places. Note that we first figure out which *place* the edge corresponds to and then 
            #determine the index of v we need to care about. 

            relevant_place          = self._edge_dict.get(e)
            relevant_place_reversed = self._edge_dict.get((end, start))

            if relevant_place == None and relevant_place_reversed != None:
                relevant_place = relevant_place_reversed
                sign = -1
            else: 
                sign = 1 

            #if e does not correspond to a relevant place, then 'self._E_dict.get(relevant_place, len(v))' will be equal to 0 
            #and hence will return the last value of v + [0] which is 0. 
            boundary_value = sign * (list(v) + [0])[self._E_dict.get(relevant_place, len(v))]


        p = (AlgebraicField()(start[0]), self.lift_pt(start[0])[start[1]])

        reversed = False
        if p[0] in self.branch_points:
            end, start = e
            reversed = True
            p = (AlgebraicField()(start[0]), self.lift_pt(start[0])[start[1]])
        

        if not hasattr(omega,'_annihilator'):
            L, inits, rho_values = self._get_initial_data(omega._f, p, local_basis = True)
            omega._annihilator = L
        else: 
            L, inits, rho_values = self._get_initial_data(omega._f, p, annihilator = omega._annihilator, local_basis = True)

        ini = [0] + [~(rho + 1) * c for rho , c in zip(rho_values, inits[0])]
        path = [AlgebraicField()(start[0]), AlgebraicField()(end[0])]

        integral = (L.annihilator_of_integral()).numerical_solution(ini = ini, path = path, eps = eps)

        if reversed: 
            integral = -integral 
            
        return integral + boundary_value
        
    def _integrate_vector(self, v, gamma, eps = 1e-16):
        #input: a vector v from a vector space over QQbar of the same dimension as H_AdR^1(C) (so what self.cohomology() outputs)
        #and an element gamma which is an element from the free module on the edges of self._upstairs_graph
        #output I(v,gamma) where I is the integration pairing between betti homology and derham cohomology. 
        
        if not hasattr(self, '_master_matrix'):
            self._master_matrix        = [[None for _ in self._upstairs_graph] for _ in self.cohomology_basis()]
            self._master_matrix_errors = [[None for _ in self._upstairs_graph] for _ in self.cohomology_basis()]

        indices_cohom = [i for i,a in enumerate(v) if a != 0]
        indices_hom   = [j for j,a in enumerate(gamma) if a != 0] 

        output = 0


        for i,j in product(indices_cohom, indices_hom):

            if (self._master_matrix[i][j]) == None or (self._master_matrix_errors[i][j] > eps): 
                #NOTE: this is the only place where we integrate edges, the orientation of the edge will always be as they occur 
                #in self._upstairs_graph. The orientation is then determined by the coefficient of gamma, as below 
                self._master_matrix[i][j] = self._integrate_edge(self._cohomology_basis[i], self._upstairs_graph[j], eps = eps)
                self._master_matrix_errors[i][j] = eps

            output +=  v[i] * gamma[j] * self._master_matrix[i][j]

        return output 

    def _full_master_matrix(self): 

        V,_,_ = self.cohomology()

        if not hasattr(self, '_plane_verts'):
            self._set_plane_graph()
        if not hasattr(self, '_upstairs_graph'):
            self._set_upstairs_graph()

        for v,e in product(V.basis(), (IntegerRing() ** len(self._upstairs_graph)).basis()): 
            self._integrate_vector(v,e)

        return self._master_matrix
 
    def period_matrix(self, eps = 1e-16):

        if hasattr(self, '_period_matrix'):
            if self._period_eps < eps:
                return self._period_matrix


        V,_,_ = self.cohomology()
        H     = self.homology_basis()
        
        self._period_matrix = matrix([[self._integrate_vector(v,gamma, eps = eps) for v in V.basis()] for gamma in H])
        self._period_eps    = eps 

        return self._period_matrix

