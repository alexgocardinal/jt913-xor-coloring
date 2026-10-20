# Jensen--Toft 9.13: exact graph construction

`jt913_graph.py` uses only the Python standard library. Its vertices are the
lexicographically ordered `k`-subsets of `0,...,n-1`, and it joins two vertices
exactly when their intersection has size less than `t`.

For `n=2k=2^m` and `t=k-1`, it assigns the color `S △ {XOR(S)}`. The palette
entries are the zero-XOR `(k-1)`- and `(k+1)`-subsets; their fibers are Johnson
stars and tops of size `k+1`. Mathematical proof of optimality is independent
of these finite checks.

Run from this directory:

```sh
python3 jt913_graph.py                       # K(8,4,3); writes K8_4_3.json and K8_4_3.g6
python3 -m unittest -v test_jt913_graph.py   # K(2,1,0), K(4,2,1), K(8,4,3), K(5,2,1)
python3 jt913_graph.py --n 4 --k 2 --t 1 --out K4_2_1
```

The supplied `K8_4_3.json` lists all 70 vertices and 1,855 edges through
zero-based adjacency lists, its 14 color classes, and the graph6 string. The
separate `K8_4_3.g6` is identical to the graph6 file in the uploaded archive.
The JSON uses expanded names (`vertex_count`, `edge_count`, `parameters`) but
its vertex, adjacency, palette, color, and graph6 fields match the uploaded
witness entry for entry. The generator limits explicit output to 1,000
vertices by default, since K(16,8,7) has 12,870 vertices and more than
80 million edges. Individual color assignments and fibers work without
constructing the graph, at any power-of-two order.
