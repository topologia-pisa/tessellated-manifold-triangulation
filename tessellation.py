from abc import ABC, abstractmethod, abstractproperty
from typing import Any, Callable, Dict, List, Tuple, Type, cast
import regina, itertools, signal
from regina import Triangulation5
from regina.engine import Face5_0, Simplex5
from sage.all import Graph, SimplicialComplex
from sage.modular.pollack_stevens.space import ManinMap


def get_link(vertex):
    """
    Gets the link of a vertex by hand, since Regina
    did not support it in high dimension.
    """
    d = vertex.triangulation().dimension
    embeddings = vertex.embeddings()
    link_simplices = {}
    link = regina.__getattribute__("Triangulation" + str(d - 1))()
    for e in embeddings:
        assert (e.simplex().index(), e.vertex()) not in link_simplices.keys()
        link_simplices[(e.simplex().index(), e.vertex())] = link.newSimplex()

    for e in embeddings:
        s = e.simplex()
        for i in range(d + 1):
            adj_s = s.adjacentSimplex(i)
            if i != e.vertex() and adj_s is not None:
                # Create restricted permutation
                old_simplex_vertices = [x for x in range(d + 1) if x != e.vertex()]
                new_simplex_vertices = [
                    x for x in range(d + 1) if x != s.adjacentGluing(i)[e.vertex()]
                ]
                p = [
                    new_simplex_vertices.index(
                        s.adjacentGluing(i)[old_simplex_vertices[j]]
                    )
                    for j in range(d)
                ]
                assert sorted(p) == list(range(d))
                Permutation = regina.__getattribute__("Perm" + str(d))
                link_simplices[(s.index(), e.vertex())].join(
                    old_simplex_vertices.index(i),
                    link_simplices[(adj_s.index(), s.adjacentGluing(i)[e.vertex()])],
                    Permutation(*p) if d <= 5 else Permutation(p),
                )

    return link


Face5_0.get_link = get_link


def identify_with(simplex1, simplex2, perm):
    """Removes simplex1 and glue adjacent simplices to simplex2"""
    d = simplex1.triangulation().dimension
    if simplex1 == simplex2:
        assert perm.isIdentity()
        return
    else:
        # Do not allow identification of glued simplices
        assert simplex2 not in [simplex1.adjacentSimplex(i) for i in range(d + 1)]

    gluings = [
        (simplex1.adjacentSimplex(i), simplex1.adjacentGluing(i)) for i in range(d + 1)
    ]
    simplex1.isolate()
    for i in range(d + 1):
        adj_s, adj_g = gluings[i]
        if simplex2.adjacentSimplex(perm[i]) is None and adj_s is not None:
            simplex2.join(perm[i], adj_s, adj_g * perm.inverse())
    simplex1.triangulation().removeSimplex(simplex1)


Simplex5.identify_with = identify_with


def simplicial_complex_from_triangulation(triangulation):
    simpl_cplx = []
    d = triangulation.dimension
    for s in triangulation.simplices():
        for indices in itertools.product(*[list(range(n)) for n in range(2, d + 2)]):
            # indices ranges among d-uples in which the i-th element is between 0 and i.
            simpl = [(d, s.index())]
            f = s
            for i, j in enumerate(reversed(indices)):
                f = f.face(d - i - 1, j)
                simpl.append((d - i - 1, f.index()))
                simpl_cplx.append(simpl)
                return SimplicialComplex(simpl_cplx)


Triangulation5.get_simplicial_complex = simplicial_complex_from_triangulation


class AbstractPolytopeIsometry:
    def inverse(self):
        raise NotImplementedError(
            "Please implement inverse function in the appropriate subclass."
        )

    def __eq__(self, other):
        raise NotImplementedError(
            "Please implement __eq__ function in the appropriate subclass."
        )

    def __mul__(self, other):
        raise NotImplementedError(
            "Please implement __mul__ function in the appropriate subclass."
        )

    def __call__(self, arg, other_pol):
        """
        Should return the image of a facet in the polytope other_pol (if omitted, self should be used).
        """
        raise NotImplementedError(
            "Please implement __call__ function in the appropriate subclass."
        )


class AbstractPolytope(ABC):
    dimension: int
    facet_class: Type["AbstractFacet"]
    facet_graph: Graph

    def __init__(self):
        self.facets = {
            i: self.facet_class(i, self) for i in self.facet_graph.vertices()
        }

    def triangulate(self, tri):
        for f in self.facets.values():
            f.triangulate(tri)

        for f1, f2, _ in self.facet_graph.edges():
            self.facets[f1].interior_join(self.facets[f2])


class AbstractFacet(ABC):
    def __init__(self, index, pol: AbstractPolytope):
        self.index = index
        self.pol = pol
        self.state = None
        self.adjacent_pol = None
        self.joining_iso = None

    def triangulate(self, tri):
        """
        Constructs a triangulation of the cone on the facet.
        """
        raise NotImplementedError()

    def interior_join(self, other_facet):
        """
        Joins the triangulation with another facet in the same polytope.
        """
        raise NotImplementedError()

    def interior_unjoin(self, other_facet):
        """
        Unjoins the triangulation with another facet in the same polytope.
        """
        raise NotImplementedError()

    def exterior_join(self, pol, iso):
        """
        Joins the external boundary with another facet on another polytope, via a given isometry.
        """
        raise NotImplementedError()


class Cell(AbstractPolytope):
    manifold: "Tessellated_manifold"
    index: int


class Panel(AbstractFacet):
    polytope: Cell
    state: bool | None


class Tessellated_manifold:
    def __init__(
        self,
        polytope: Type[AbstractPolytope],
        indices: List[Any],
        pasting_map: Callable[[AbstractFacet], Tuple[Cell, AbstractPolytopeIsometry]],
        state: Callable[[AbstractFacet], bool] | None = None,
    ):
        """
        Builds a manifold tessellated with copies of polytope, which are indexed by indices.
        pasting_map takes a facet as input and must return a 2-uple (glued polytope, isomorphism),
        and None if it is a boundary facet.
        state, if provided, takes a facet as input and return True if it is pointing outwards, False if inwards.
        """
        self.polytope_class = polytope
        self.polytopes: Dict[Any, Cell] = {}

        for i in indices:
            self.polytopes[i] = cast(Cell, polytope())
            self.polytopes[i].index = i
            self.polytopes[i].manifold = self

        # Set states
        if state is not None:
            for p in self.polytopes.values():
                for f in p.facets.values():
                    f.state = state(f)

        # Paste facets
        for p in self.polytopes.values():
            for f in p.facets.values():
                if pasting_map(f) is not None:
                    target_p, iso = pasting_map(f)
                    target_f = iso(f, target_p)
                    # Controlla che la mappa di incollamento sia simmetrica
                    assert pasting_map(target_f) == (p, iso.inverse())
                    assert target_f.state is None or target_f.state == (not f.state)
                    # Incollamento
                    f.adjacent_pol = target_p
                    f.joining_iso = iso

        self.tri = self.triangulate()

    def __repr__(self):
        """
        Pretty prints a table with all information on
        gluing isomophisms and states.
        """
        ret = ""
        for p in self.polytopes.values():
            ret += (
                "Polytope "
                + str(p.index)
                + "\n{:<24}{:<8}{:<12}{:<24}{:<12}\n".format(
                    "Facet", "Status", "To Polytope", "To Facet", "Permutation"
                )
            )
            for f in p.facets.values():
                ret += "{:<24}{:<8}{:<12}{:<24}{:<12}\n".format(
                    str(f.index),
                    "Out" if f.state else "In",
                    str(f.adjacent_pol.index),
                    str(f.joining_iso(f).index),
                    str(f.joining_iso.perm),
                )
        return ret

    def triangulate(self):
        """
        Returns a triangulation for the manifold, obtained by
        triangulation the single polytopes and then gluing together
        pasted factes.
        """
        tri = regina.__getattribute__(
            "Triangulation" + str(self.polytope_class.dimension)
        )()
        for p in self.polytopes.values():
            p.triangulate(tri)
        for p in self.polytopes.values():
            for f in p.facets.values():
                if f.adjacent_pol is not None:
                    f.exterior_join(f.adjacent_pol, f.joining_iso)

        return tri

    def get_triangulation_cut_along_fiber(self):
        """
        Cuts the triangulation between facets with opposite
        states.
        """
        for p in self.polytopes.values():
            for f1, f2, _ in p.facet_graph.edges():
                if p.facets[f1].state == (not p.facets[f2].state):
                    p.facets[f1].interior_unjoin(p.facets[f2])

        product = self.tri.__class__(self.tri)
        for p in self.polytopes.values():
            for f1, f2, _ in p.facet_graph.edges():
                if p.facets[f1].state == (not p.facets[f2].state):
                    p.facets[f1].interior_join(p.facets[f2])
        return product

    def get_fiber(self):
        """
        Returns a triangulation of the fiber as a boundary
        component of the cut triangulation above.
        """
        t = self.get_triangulation_cut_along_fiber()
        fibers = [b.build() for b in t.boundaryComponents()]
        assert all(f.isIsomorphicTo(fibers[0]) for f in fibers)
        return fibers[0]

    def get_quotient(self, isometry_group):
        """
        Returns the quotient of the manifold by a given isometry group.
        If the manifold has boundary (for finiteness reasons) there must be at least a representative of each
        orbit in the interior.
        """
        representatives = []
        for p in self.polytopes.values():
            p.identification = None

        for p in self.polytopes.values():
            if p.identification is None and all(
                f.adjacent_pol is not None for f in p.facets.values()
            ):
                for phi in isometry_group:
                    if phi(p) is not None:
                        phi(p).identification = phi.inverse()
                        assert all(
                            not hasattr(f, "state") or f.state == phi(f).state
                            for f in p.facets.values()
                        )
                representatives.append(p.index)
                assert p.identification is not None

        def facet_mapping(f):
            p = f.pol
            m = p.manifold
            upper_adj_pol = self.polytopes[p.index].facets[f.index].adjacent_pol
            if upper_adj_pol is not None:
                return (
                    m.polytopes[upper_adj_pol.identification(upper_adj_pol).index],
                    upper_adj_pol.identification.isos.get(upper_adj_pol.index)
                    * self.polytopes[p.index].facets[f.index].joining_iso,
                )
            else:
                return None

        def facet_state(f):
            return self.polytopes[f.pol.index].facets[f.index].state

        ret = Tessellated_manifold(
            self.polytope_class, representatives, facet_mapping, facet_state
        )
        ret.covering = self
        return ret

    def get_finite_cover(self, n):
        """
        Returns the finite cover with respect to the given states.
        """

        def facet_mapping(f):
            p = f.pol
            m = p.manifold
            index, level = p.index
            covered_facet = self.polytopes[p.index[0]].facets[f.index]
            if covered_facet.adjacent_pol is None:
                return None
            else:
                return (
                    m.polytopes[
                        (
                            covered_facet.adjacent_pol.index,
                            (level + (1 if covered_facet.state else -1)) % n,
                        )
                    ],
                    covered_facet.joining_iso,
                )

        def facet_state(f):
            return self.polytopes[f.pol.index[0]].facets[f.index].state

        return Tessellated_manifold(
            self.polytope_class,
            [(p, k) for p in self.polytopes for k in range(n)],
            facet_mapping,
            facet_state,
        )


class Tessellated_manifold_isometry:
    def __init__(
        self, manifold, start_pol=None, end_pol=None, iso=None, images=None, isos=None
    ):
        """
        Defines an isometry of a manifold that sends a polytope in another with a given isomorphism.
        If more are provided, fewer computations are needed.
        """
        self.manifold = manifold

        if start_pol is not None:
            assert end_pol is not None
            self.images = {start_pol.index: end_pol}
            self.isos = {start_pol.index: iso}
        else:
            self.images = {k: v for k, v in images.items() if v is not None}
            self.isos = {k: v for k, v in isos.items() if v is not None}
            assert self.images.keys() == self.isos.keys()

        # assert self.images
        self.unmapped = []
        self.polytope_class = manifold.polytope_class

        def compute_adjacent_maps(i):
            p = manifold.polytopes[i]
            for f in p.facets.values():
                if (
                    f.adjacent_pol is not None
                    and f.adjacent_pol.index not in self.unmapped
                    and f.adjacent_pol.index not in self.images
                ):
                    target_f = self(f)
                    if target_f.adjacent_pol is not None:
                        self.images.update(
                            {f.adjacent_pol.index: target_f.adjacent_pol}
                        )
                        self.isos.update(
                            {
                                f.adjacent_pol.index: target_f.joining_iso
                                * self.isos[i]
                                * f.joining_iso.inverse()
                            }
                        )
                        compute_adjacent_maps(f.adjacent_pol.index)
                    else:
                        self.unmapped.append(f.adjacent_pol.index)

        for i in list(self.images.keys()):
            compute_adjacent_maps(i)

    def inverse(self):
        return Tessellated_manifold_isometry(
            self.manifold,
            images={
                v.index: self.manifold.polytopes[k] for k, v in self.images.items()
            },
            isos={self.images[k].index: v.inverse() for k, v in self.isos.items()},
        )

    def __eq__(self, other):
        for k in self.images:
            # Only need to check one element
            return self.images.get(k) == other.images.get(k) and self.isos.get(
                k
            ) == other.isos.get(k)

        return other.images == {}

    def __call__(self, arg):
        if isinstance(arg, self.polytope_class):
            return self.images.get(arg.index)
        else:
            target_pol = self.images.get(arg.pol.index)
            if target_pol is not None:
                return self.isos.get(arg.pol.index)(arg, target_pol)
            else:
                return None

    def __mul__(self, other):
        return Tessellated_manifold_isometry(
            self.manifold,
            images={k: self.images.get(v.index) for k, v in other.images.items()},
            isos={
                k: self.isos.get(v.index) * other.isos.get(k)
                for k, v in other.images.items()
                if v.index in self.isos
            },
        )

    def __bool__(self):
        return bool(self.images)


class Tessellated_manifold_isometry_group:
    def __init__(self, *generators, iterations=-1):
        """
        Computes the isometry group given some generators.
        Each iteration checks if the product of every pair of elements is already in the group,
        and if not adds it, until no more new elements can be found.
        If iterations is provided, stops after the corresponding number of iterations.
        It can also be stopped by pressing Ctrl-C, if you are sure that every element is already been found.
        """
        new_elements = list(generators)
        id = generators[0] * generators[0].inverse()
        if id not in new_elements:
            new_elements.append(generators[0] * generators[0].inverse())
        self.elements = []

        original_sigint_handler = signal.getsignal(signal.SIGINT)
        global interrupted
        interrupted = False

        def sigint_handler(sig, frame):
            global interrupted
            interrupted = True

        signal.signal(signal.SIGINT, sigint_handler)
        print("Computing isometry group... Press Ctrl-C to terminate early.")
        while new_elements and iterations != 0 and not interrupted:
            if self.elements != []:
                print("Moving to next iteration...")
            iterations -= 1
            found = []
            for a, b in itertools.product(self.elements + new_elements, new_elements):
                c = a * b.inverse()
                if c is not None and c not in self.elements + new_elements + found:
                    found.append(c)
                    print(
                        "Found {} new elements, total {}...".format(
                            len(found),
                            len(found) + len(self.elements) + len(new_elements),
                        ),
                        end="\r",
                    )
                if interrupted:
                    break
            self.elements += new_elements
            new_elements = found
            print(
                "Found {num} new elements, total {tot}.  ".format(
                    num=len(new_elements), tot=len(self.elements) + len(new_elements)
                ),
                end="\b",
            )
        print("Done.")
        signal.signal(signal.SIGINT, original_sigint_handler)
        self.elements += new_elements

    def __iter__(self):
        return iter(self.elements)

    def get_orbit(self, pol):
        return [phi(pol) for phi in self.elements]
