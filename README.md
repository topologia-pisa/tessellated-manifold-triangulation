# tessellated-manifold-triangulation

This is a little script to help investigate the manifolds built in [arXiv:2105.147955](https://arxiv.org/abs/2105.14795), by using the software [Regina](https://regina-normal.github.io/).

### Requirements

Make sure python3 and Sage are installed. Install Regina with

```
$ pip install regina
```

Clone this repo in your favourite dierectory:

```
$ cd <your-favourite-directory>
$ git clone https://github.com/topologia-pisa/tessellated-manifold-triangulation
$ cd tessellated-manifold-triangulation
```

### Testing

You can run `M5.py` in interactive mode to inspect the manifolds with

```
$ python3 -i M5.py
```

The above command might not work if you're not running the python binary which is bundled with Sage.
If it doesn't work, you may also try to run Sage directly with

```
$ sage -python -i M5.py
```

(thanks to Colby Kelln for pointing that out).

From here you have at your disposal some functions which build a manifold, for example

```
>>> M=get_minimal_quotient()
Computing isometry group... Press Ctrl-C to terminate early.
Found 1 new elements, total 3. Moving to next iteration...
Found 1 new elements, total 4. Moving to next iteration...
Found 2 new elements, total 6. Moving to next iteration...
Found 2 new elements, total 8. Moving to next iteration...
Found 0 new elements, total 8. Done.
```

You can get a description of what the manifold is supposed to be with

```
>>> help(get_minimal_quotient)

Help on function get_minimal_quotient in module M5:

get_minimal_quotient()
    Constructs a small manifold gluing two copies of P5, using Q8.
    The result is isomorphic to the manifold constructed by Ratcliffe and Tschantz.
```

You can also print a combinatorial description of how the facets are pasted to each other:

```
>>> M
Polytope (0, 1)
Facet                   Status  To Polytope To Facet                Permutation
(-1, -1, -1, -1, 1)     In      (0, -1)     (-1, 1, 1, 1, -1)       02134
(-1, -1, -1, 1, -1)     In      (0, 1)      (1, 1, -1, -1, 1)       31204
(-1, -1, 1, -1, -1)     In      (0, 1)      (1, -1, 1, -1, 1)       13024
(-1, -1, 1, 1, 1)       In      (0, -1)     (1, 1, 1, -1, -1)       31204
(-1, 1, -1, -1, -1)     In      (0, 1)      (1, -1, -1, 1, 1)       20314
(-1, 1, -1, 1, 1)       In      (0, -1)     (1, 1, -1, 1, -1)       20314
(-1, 1, 1, -1, 1)       In      (0, -1)     (1, -1, 1, 1, -1)       13024
(-1, 1, 1, 1, -1)       Out     (0, -1)     (-1, -1, -1, -1, 1)     02134
(1, -1, -1, -1, -1)     In      (0, 1)      (1, 1, 1, 1, 1)         02134
(1, -1, -1, 1, 1)       Out     (0, 1)      (-1, 1, -1, -1, -1)     13024
(1, -1, 1, -1, 1)       Out     (0, 1)      (-1, -1, 1, -1, -1)     20314
(1, -1, 1, 1, -1)       Out     (0, -1)     (-1, 1, 1, -1, 1)       20314
(1, 1, -1, -1, 1)       Out     (0, 1)      (-1, -1, -1, 1, -1)     31204
(1, 1, -1, 1, -1)       Out     (0, -1)     (-1, 1, -1, 1, 1)       13024
(1, 1, 1, -1, -1)       Out     (0, -1)     (-1, -1, 1, 1, 1)       31204
(1, 1, 1, 1, 1)         Out     (0, 1)      (1, -1, -1, -1, -1)     02134
Polytope (0, -1)
Facet                   Status  To Polytope To Facet                Permutation
(-1, -1, -1, -1, 1)     In      (0, 1)      (-1, 1, 1, 1, -1)       02134
(-1, -1, -1, 1, -1)     In      (0, -1)     (1, 1, -1, -1, 1)       31204
(-1, -1, 1, -1, -1)     In      (0, -1)     (1, -1, 1, -1, 1)       13024
(-1, -1, 1, 1, 1)       In      (0, 1)      (1, 1, 1, -1, -1)       31204
(-1, 1, -1, -1, -1)     In      (0, -1)     (1, -1, -1, 1, 1)       20314
(-1, 1, -1, 1, 1)       In      (0, 1)      (1, 1, -1, 1, -1)       20314
(-1, 1, 1, -1, 1)       In      (0, 1)      (1, -1, 1, 1, -1)       13024
(-1, 1, 1, 1, -1)       Out     (0, 1)      (-1, -1, -1, -1, 1)     02134
(1, -1, -1, -1, -1)     In      (0, -1)     (1, 1, 1, 1, 1)         02134
(1, -1, -1, 1, 1)       Out     (0, -1)     (-1, 1, -1, -1, -1)     13024
(1, -1, 1, -1, 1)       Out     (0, -1)     (-1, -1, 1, -1, -1)     20314
(1, -1, 1, 1, -1)       Out     (0, 1)      (-1, 1, 1, -1, 1)       20314
(1, 1, -1, -1, 1)       Out     (0, -1)     (-1, -1, -1, 1, -1)     31204
(1, 1, -1, 1, -1)       Out     (0, 1)      (-1, 1, -1, 1, 1)       13024
(1, 1, 1, -1, -1)       Out     (0, 1)      (-1, -1, 1, 1, 1)       31204
(1, 1, 1, 1, 1)         Out     (0, -1)     (1, -1, -1, -1, -1)     02134
```

Also, you can access the Regina triangulation of the manifold via the `tri` attribute of `M`:

```
>>> M.tri
<regina.Triangulation5: Possibly closed orientable 5-D triangulation, f = ( 5 67 320 640 576 192 )>
```

As an example, we check that the manifold built by Ratcliffe and Tschantz is isomorphic to M, by making use of Regina's [isIsomorphic](https://regina-normal.github.io/engine-docs/classregina_1_1detail_1_1TriangulationBase.html#ac568895b8abeb672289fcee779ebf01a) function:

```
>>> help(get_rt_minimal_manifold)

Help on function get_rt_minimal_manifold in module M5:

get_rt_minimal_manifold()
    Constructs the manifold described by Ratcliffe and Tschantz.

>>> R=get_rt_minimal_manifold()
>>> M.tri.isIsomorphicTo(R.tri)
<regina.Isomorphism5: 0 -> 60 (051432), 1 -> 65 (051432), 2 -> 61 (051432), 3 -> 64 (051432), 4 -> 63 (051432),
5 -> 62 (051432), 6 -> 72 (051432), 7 -> 77 (051432), 8 -> 73 (051432), 9 -> 76 (051432), 10 -> 75 (051432),
11 -> 74 (051432), 12 -> 90 (051432), 13 -> 95 (051432), 14 -> 91 (051432), 15 -> 94 (051432), 16 -> 93 (051432),
17 -> 92 (051432), 18 -> 54 (051432), 19 -> 59 (051432), 20 -> 55 (051432), 21 -> 58 (051432), 22 -> 57 (051432),
23 -> 56 (051432), 24 -> 36 (051432), 25 -> 41 (051432), 26 -> 37 (051432), 27 -> 40 (051432), 28 -> 39 (051432),
29 -> 38 (051432), 30 -> 0 (051432), 31 -> 5 (051432), 32 -> 1 (051432), 33 -> 4 (051432), 34 -> 3 (051432),
35 -> 2 (051432), 36 -> 18 (051432), 37 -> 23 (051432), 38 -> 19 (051432), 39 -> 22 (051432), 40 -> 21 (051432),
41 -> 20 (051432), 42 -> 30 (051432), 43 -> 35 (051432), 44 -> 31 (051432), 45 -> 34 (051432), 46 -> 33 (051432),
47 -> 32 (051432), 48 -> 84 (051432), 49 -> 89 (051432), 50 -> 85 (051432), 51 -> 88 (051432), 52 -> 87 (051432),
53 -> 86 (051432), 54 -> 48 (051432), 55 -> 53 (051432), 56 -> 49 (051432), 57 -> 52 (051432), 58 -> 51 (051432),
59 -> 50 (051432), 60 -> 66 (051432), 61 -> 71 (051432), 62 -> 67 (051432), 63 -> 70 (051432), 64 -> 69 (051432),
65 -> 68 (051432), 66 -> 78 (051432), 67 -> 83 (051432), 68 -> 79 (051432), 69 -> 82 (051432), 70 -> 81 (051432),
71 -> 80 (051432), 72 -> 12 (051432), 73 -> 17 (051432), 74 -> 13 (051432), 75 -> 16 (051432), 76 -> 15 (051432),
77 -> 14 (051432), 78 -> 24 (051432), 79 -> 29 (051432), 80 -> 25 (051432), 81 -> 28 (051432), 82 -> 27 (051432),
83 -> 26 (051432), 84 -> 42 (051432), 85 -> 47 (051432), 86 -> 43 (051432), 87 -> 46 (051432), 88 -> 45 (051432),
89 -> 44 (051432), 90 -> 6 (051432), 91 -> 11 (051432), 92 -> 7 (051432), 93 -> 10 (051432), 94 -> 9 (051432),
95 -> 8 (051432), 96 -> 168 (045312), 97 -> 172 (045312), 98 -> 173 (045312), 99 -> 171 (045312),
100 -> 169 (045312), 101 -> 170 (045312), 102 -> 96 (045312), 103 -> 100 (045312), 104 -> 101 (045312),
105 -> 99 (045312), 106 -> 97 (045312), 107 -> 98 (045312), 108 -> 156 (045312), 109 -> 160 (045312),
110 -> 161 (045312), 111 -> 159 (045312), 112 -> 157 (045312), 113 -> 158 (045312), 114 -> 132 (045312),
115 -> 136 (045312), 116 -> 137 (045312), 117 -> 135 (045312), 118 -> 133 (045312), 119 -> 134 (045312),
120 -> 144 (045312), 121 -> 148 (045312), 122 -> 149 (045312), 123 -> 147 (045312), 124 -> 145 (045312),
125 -> 146 (045312), 126 -> 120 (045312), 127 -> 124 (045312), 128 -> 125 (045312), 129 -> 123 (045312),
130 -> 121 (045312), 131 -> 122 (045312), 132 -> 180 (045312), 133 -> 184 (045312), 134 -> 185 (045312),
135 -> 183 (045312), 136 -> 181 (045312), 137 -> 182 (045312), 138 -> 108 (045312), 139 -> 112 (045312),
140 -> 113 (045312), 141 -> 111 (045312), 142 -> 109 (045312), 143 -> 110 (045312), 144 -> 150 (045312),
145 -> 154 (045312), 146 -> 155 (045312), 147 -> 153 (045312), 148 -> 151 (045312), 149 -> 152 (045312),
150 -> 126 (045312), 151 -> 130 (045312), 152 -> 131 (045312), 153 -> 129 (045312), 154 -> 127 (045312),
155 -> 128 (045312), 156 -> 186 (045312), 157 -> 190 (045312), 158 -> 191 (045312), 159 -> 189 (045312),
160 -> 187 (045312), 161 -> 188 (045312), 162 -> 114 (045312), 163 -> 118 (045312), 164 -> 119 (045312),
165 -> 117 (045312), 166 -> 115 (045312), 167 -> 116 (045312), 168 -> 174 (045312), 169 -> 178 (045312),
170 -> 179 (045312), 171 -> 177 (045312), 172 -> 175 (045312), 173 -> 176 (045312), 174 -> 102 (045312),
175 -> 106 (045312), 176 -> 107 (045312), 177 -> 105 (045312), 178 -> 103 (045312), 179 -> 104 (045312),
180 -> 162 (045312), 181 -> 166 (045312), 182 -> 167 (045312), 183 -> 165 (045312), 184 -> 163 (045312),
185 -> 164 (045312), 186 -> 138 (045312), 187 -> 142 (045312), 188 -> 143 (045312), 189 -> 141 (045312),
190 -> 139 (045312), 191 -> 140 (045312)>
```
