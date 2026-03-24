from sage.rings.function_field.constructor import FunctionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.matrix.constructor import matrix
from sage.arith.functions import lcm
from sage.hodge_theory import auxiliary
from sage.categories.homset import Hom
from sage.rings.qqbar import AlgebraicField
from sage.rings.rational_field import RationalField
from sage.rings.qqbar import number_field_elements_from_algebraics
from sage.modules.free_module_element import vector
from sage.symbolic.constants import I
from sage.rings.complex_mpfr import ComplexField
from sage.rings.real_mpfr import RealField
from sage.all import arg, log



def voronoi(pts):

    from sage.geometry.voronoi_diagram import VoronoiDiagram

    smallest_dist = min([
        AlgebraicField()(abs(alpha - beta)) for alpha in pts for beta in pts 
        if alpha != beta 
    ])

    print(smallest_dist)
    print(log(smallest_dist, 2))
    print(RealField()(log(smallest_dist, 2)))

    prec = int(-RealField()(log(smallest_dist, 2))) + 53

    C = ComplexField(prec = prec)

    centre = sum(pts)/len(pts)
    radius = 2 * max([abs(centre - z) for z in pts])
    z = AlgebraicField().zeta(6)
    circle_points = [C(centre + radius * z ** i) for i in range(6)]

    return VoronoiDiagram([C(v) for v in pts] + circle_points)



class MixedHodgeStructure:

    def __init__(self, P, D, E):
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
            inf_divisors = [
                OCoo.ideal(1/x, OCoo.basis()[1] - p[1]/p[0]).divisor()
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

            #here we define the places corresponding to E. we do this over QQbar for now but this can be done more generally
            if hasattr(self, '_E_places'):
                places = self._E_places
            else: 
                OC = self._function_field_Qbar.maximal_order()
                x,y = OC(self._x), OC(self._y)
                places = [p for e in self._E for p in OC.ideal(x - e[0], y - e[1]).divisor().support()]
                self._E_places = places

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
        V, f, _ = self.cohomology()
        return [f(v) for v in V.basis()]
    
    def _lift_pt(self, v):
        t = PolynomialRing(AlgebraicField(), names = '')
        return self._P(v, t).roots(multiplicities = False)


    def _set_plane_graph(self):

        t = PolynomialRing(AlgebraicField(), names = 't').gen()

        self.branch_points = self._P.discriminant(self._P.parent().gens()[1])(t,0).roots(multiplicities = False)

        self.branch_points_and_xD = self.branch_points + [x[0] for x in self._D if x[0] not in self.branch_points]  

        V = voronoi(self.branch_points_and_xD)
        self._voronoi_graph = V
        
        relevant_points = V.points()[:len(self.branch_points_and_xD)]
        relevant_regions = [V.regions().get(p) for p in relevant_points]
        self._plane_verts = list(set([
            RationalField()(v[0]) + RationalField()(v[1]) * I 
            for R in relevant_regions for v in R.vertices()
            ]))
        
        self._plane_edges = []
        self._plane_loops = []

        for p in relevant_points:
            local_centre = RationalField()(list(p)[0]) + RationalField()(list(p)[1]) * I
            local_vertices = [
                RationalField()(list(v)[0]) + RationalField()(list(v)[1]) * I
                for v in V.regions().get(p).vertices()
            ]    
            local_vertices.sort(key = lambda z : arg(local_centre - z))
            
            new_edges = list(zip(local_vertices, local_vertices[1:] + local_vertices[:1]))

            self._plane_loops.append(new_edges)
            self._plane_edges.extend([e for e in new_edges])

        infinite_regions = [V.regions().get(p) for p in V.points()[len(self.branch_points_and_xD):]]
        outside_vertices = [
            RationalField()(v[0]) + RationalField()(v[1]) * I
            for R in infinite_regions for v in R.vertices()
            ]
        
        c = sum(outside_vertices)/len(outside_vertices)
        outside_vertices.sort(key = lambda z : arg(z - c))
        self._plane_loops.append(list(zip(outside_vertices, outside_vertices[1:] + outside_vertices[:1])))


        for e in self._E:
            if e[0] not in self._plane_verts:
                print('hi')
                close_to_e = min(
                    self._plane_verts,
                    key = lambda z : abs(z - e[0]) 
                    )
                self._plane_verts += [e[0]]
                self._plane_edges.append((e[0], close_to_e))
                


    def homology(self):

        if not hasattr(self, '_plane_verts'):
            self._set_plane_graph()

      
