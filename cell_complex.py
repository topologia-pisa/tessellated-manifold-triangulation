class Cell:
    def __init__(self, dimension, boundary, index=None):
        self.dimension = dimension
        self.boundary = boundary
        self.index = index

    def __repr__(self):
        return "{}-cell with index {}".format(self.dimension, self.index)

    def __sum__(self, other):
        return CellChain(self) + other

    def __rsum__(self, other):
        return other + CellChain(self)

    def __neg__(self):
        return -CellChain(self)

class CellChain:
    def __init__(self, arg):
        if arg.__class__ is int:
            self.components = dict()
            self.dimension = arg
        elif arg.__class__ is dict:
            self.components = arg
            [self.dimension] = [c.dimension for c in self.components]
        else:
            self.components = {arg: 1}
            self.dimension = arg.dimension

    def get_cells(self):
        return set(x for x in self.components if self.get_components(x) != 0)
    cells = property(get_cells)

    def get_component(cell):
        return self.components[cell] if cell in self.components else 0

    def __sum__(self, other):
        return CellChain({c: self.get_component(c) + other.get_component(c) for c in self.cells.union(other.cells)})

    def __neg__(self):
        return CellChain({c: -self.get_component(c) for c in self.components})

class Cube(Cell):
    def __init__(self, dimension, face, index=None):
        """
        face(n, upper) must return the n-th upper (if upper is 1 or True) or lower face of the cube.
        """
        self.face = face
        self.dimension = dimension
        self.index = index
        assert all(f.dimension == self.dimension - 1 for f in self.faces())
        self.fiber = dict()

    def faces(self):
        """
        The list of faces (of codimension 1) of this cube
        """
        return self.lower_faces() + self.upper_faces()

    def faces_as_pairs(self):
        """
        The list of faces (of codimension 1) of this cube, as pairs
        (upper, lower).
        """
        return list(zip(self.upper_faces, self.lower_faces))

    def lower_faces(self):
        return [self.face(i, False) for i in range(self.dimension)]

    def upper_faces(self):
        return [self.face(i, True) for i in range(self.dimension)]

    def get_fiber(self, level):
        if level not in self.fiber:
            self.fiber[level] = CubeFiber(self, level, self.index)
        return self.fiber[level]

class CubeFiber(Cell):
    """
    Represents the level set of an open cube.
    """
    def __init__(self, cube, level, index=None):
        self.cube = cube
        self.level = level
        self.index = index
        if level <= 0 or level >= cube.dimension:
            self.dimension = -1 # Counterimage is empty
        else:
            self.dimension = cube.dimension - 1

        self.boundary = []
        for c in cube.lower_faces():
            f = c.get_fiber(level)
            if f.dimension == self.dimension - 1:
                self.boundary.append(f)

        for c in cube.upper_faces():
            f = c.get_fiber(level - 1)
            if f.dimension == self.dimension - 1:
                self.boundary.append(f)
