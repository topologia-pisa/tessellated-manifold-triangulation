import itertools, json, os, sys
from sage.all import product, QuaternionAlgebra, Matrix, Permutation, vector
from regina import Perm4, Perm5, Perm6, Triangulation5

Quaternions = QuaternionAlgebra(-1, -1)
I,J,K = Quaternions.gen(0), Quaternions.gen(1), Quaternions.gen(2)

with open(os.path.join(sys.path[0], 'ratcliffe-tschantz.json')) as f:
    rt = json.load(f)
    for m in rt["pasting_matrices"].values():
        assert Matrix(m).transpose() * Matrix.diagonal([1,1,1,1,1,-1]) * Matrix(m) == Matrix.diagonal([1,1,1,1,1,-1]), m

class P5_iso:
    def __init__(self, refl=[1,1,1,1,1], perm=Perm5()):
        # Definisce un isomorfismo di P5 che permuta le componenti e fa una riflessione.
        if len(refl)==4:
            refl.append(product(refl))
        assert len(refl)==5 and product(refl)==1, "Invalid reflection"
        self.refl = refl

        if isinstance(perm, Perm4):
            perm = Perm5.extend(perm)
        assert isinstance(perm, Perm5)
        self.perm = perm

    def inverse(self):
        phi = P5_iso(perm=self.perm.inverse())
        psi = P5_iso(self.refl)
        inv = phi * psi
        # Check composition is the identity
        assert inv * self == P5_iso(), (inv, self)
        return inv

    @classmethod
    def from_lorentzian_matrix(cls, mat):
        cusps = [vector({i: 1, 5:1}) for i in range(5)]
        cusps += [vector([1,1,1,1,1,3]) - x for x in cusps]
        assert sorted(cusps) == sorted(mat * v for v in cusps)
        return cls(perm=Perm5(*[cusps.index(mat*v) % 5 for v in cusps[0:5]]))*cls(refl=[1 if mat*v in cusps[0:5] else -1 for v in cusps[0:5]])

    def __eq__(self, other):
        return self.perm == other.perm and self.refl == other.refl

    def __mul__(self, other):
        return P5_iso([self.refl[i] * other.refl[self.perm.preImageOf(i)] for i in range(5)], self.perm*other.perm)

    def __repr__(self):
        return str((self.refl, self.perm))

    def __call__(self, arg, other_pol=None):
        # Return corresponding facet or vertex via isometry
        if other_pol is None:
            other_pol = arg.pol

        # Pemutates coordinates
        coords = tuple(arg.coords[self.perm.preImageOf(i)] for i in range(5))

        # Reflect coordinates
        coords = tuple(x * y for x, y in zip(self.refl, coords))

        if isinstance(arg, P5_facet):
            return other_pol.facets[coords]
        elif isinstance(arg, P5_vertex):
            return other_pol.vertices[coords]
        else:
            raise("Invalid argument for isometry")

class P5:
    dimension = 5
    def __init__(self, tri=None):
        self.facets = {}
        self.vertices = {}
        # If tri is provided, adds the simplex to the existing triangulation, else it creates a new one
        if tri is None:
            tri = Triangulation5()
        self.tri = tri

        for t in itertools.product(*[[1,-1]]*5):
            # cycle over 5-uples of ±1
            if product(t) == 1:
                self.facets[t] = P5_facet(t, self)
            else:
                self.vertices[t] = P5_vertex(t, self)

        for f in self.facets.values():
            for i in range(1, 6):
                # Join inner_simplices of facets with inner_simplices of adjacent vertex
                f.inner_simplex.join(i, f.adj_vertex(i).inner_simplex, Perm6())

    def identify_with(self, other_pol, iso=None):
        if iso is None:
            iso = P5_iso()
        extended_perm = Perm6([1,2,3,4,5,0]) * Perm6.extend(iso.perm) * Perm6([5,0,1,2,3,4])
        for f in self.facets.values():
            f.inner_simplex.identify_with(iso(f, other_pol).inner_simplex, extended_perm)
        for v in self.vertices.values():
            v.inner_simplex.identify_with(iso(v, other_pol).inner_simplex, extended_perm)
            v.outer_simplex.identify_with(iso(v, other_pol).outer_simplex, extended_perm)

    def facet_from_number(self, n):
        return self.facets[sorted([c for c in self.facets], key=lambda x: sum(x))[n]]

class P5_facet:
    def __init__(self, coords, pol):
        self.coords = coords
        self.pol = pol
        self.inner_simplex = self.pol.tri.newSimplex()
        self.state = None
        self.adjacent_pol = None
        self.joining_iso = None

    def adj_vertex(self, direction):
        #direction è la direzione da 1 a 5 in cui muoversi.
        assert direction >= 1 and direction <= 5
        t = self.coords[0:direction-1] + (- self.coords[direction - 1], ) + self.coords[direction:5]
        return self.pol.vertices[t]

    def get_color(self):
        # Restituisce il colore della faccia da 0 a 7
        dict = {
            ( 1, 1, 1, 1): 0,
            (-1, 1, 1, 1): 4,
            ( 1,-1, 1, 1): 5,
            ( 1,-1, 1,-1): 1,
            ( 1, 1,-1, 1): 6,
            ( 1,-1,-1, 1): 2,
            ( 1, 1, 1,-1): 7,
            ( 1, 1,-1,-1): 3
        }
        x = self.coords[0:4]
        if x in dict:
            return dict[x]
        else:
            return dict[tuple(-i for i in x)]

    color = property(get_color)

    def opposite_facet(self, fake_component=4):
        # Restituisce la faccetta con tutte le componenti invertite (tranne quella indicata):
        return self.pol.facets((-self.coords[i] if i!=fake_component else self.coords[i] for i in range(5)))

    def get_label(self):
        # Restituisce un'etichetta in Q8.
        dict = {
            ( 1, 1, 1, 1): 1,
            (-1, 1, 1, 1): 1,
            ( 1,-1, 1, 1): I,
            ( 1,-1, 1,-1): I,
            ( 1, 1,-1, 1): J,
            ( 1,-1,-1, 1): J,
            ( 1, 1, 1,-1): K,
            ( 1, 1,-1,-1): K
        }
        x = self.coords[0:4]
        if x in dict:
            return dict[x]
        else:
            return -dict[tuple(-i for i in x)]

    label = property(get_label)

    def get_reflection_matrix(self):
        if self.coords == (1,1,1,1,1):
            res = Matrix(rt.get("reflection_matrices")[2])
        elif sum(self.coords) == 1:
            perm = Permutation(sorted(range(1,6), key=lambda x: -self.coords[x-1])).inverse()
            res = Matrix(rt.get("reflection_matrices")[1])
            res.permute_rows_and_columns(perm,perm)
        elif sum(self.coords) == -3:
            perm = Permutation(sorted(range(1,6), key=lambda x: -self.coords[x-1])).inverse()
            res = Matrix(rt.get("reflection_matrices")[0])
            res.permute_rows_and_columns(perm,perm)
        assert res.transpose() * Matrix.diagonal([1,1,1,1,1,-1]) * res == Matrix.diagonal([1,1,1,1,1,-1])
        return res

    reflection_matrix = property(get_reflection_matrix)

    def get_number(self):
        return sorted([c for c in self.pol.facets], key=lambda x: sum(x)).index(self.coords)

    number = property(get_number)

    def check_state_compatibility(self, other_pol, iso):
        return all(f.state == (not iso(f, other_pol).state) for f in self.facets.values())

    def paste(self, pol, iso):
        # Pastes a facet to another one via an isometry
        target_facet = iso(self, pol)
        # Devo coniugare per estendere aggiungendo lo 0 fisso all'inizio
        self.inner_simplex.join(0, target_facet.inner_simplex, Perm6([1,2,3,4,5,0]) * Perm6.extend(iso.perm) * Perm6([5,0,1,2,3,4]))

        # Attacco le facce degli outer adiacenti
        for i in range(1,6):
            self.adj_vertex(i).outer_simplex.join(i, iso(self.adj_vertex(i), pol).outer_simplex, Perm6([1,2,3,4,5,0]) * Perm6.extend(iso.perm) * Perm6([5,0,1,2,3,4]))

        self.joining_iso = iso
        self.adjacent_pol = pol
        target_facet.joining_iso = iso.inverse()
        target_facet.adjacent_pol = self.pol

class P5_vertex:
    def __init__(self, coords, pol):
        self.coords = coords
        self.pol = pol
        self.inner_simplex = self.pol.tri.newSimplex()
        self.outer_simplex = self.pol.tri.newSimplex()
        # Join inner simplex with outer simplex over the common face
        self.inner_simplex.join(0, self.outer_simplex, Perm6())

    def adj_facet(self, direction):
        #direction è la direzione da 1 a 5 in cui muoversi.
        assert direction >= 1 and direction <= 5
        t = self.coords[0:direction-1] + (- self.coords[direction - 1], ) + self.coords[direction:5]
        return self.pol.facets[t]
