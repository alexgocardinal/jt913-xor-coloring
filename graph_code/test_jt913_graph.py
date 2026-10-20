"""Finite checks of the graph construction; the infinite claim needs proof."""

import unittest

from jt913_graph import instance, verify_instance


def independence_number(adjacency):
    """Exact branch-and-bound search for small graphs, independent of coloring."""
    n = len(adjacency)
    neighbor = [0] * n
    for i, row in enumerate(adjacency):
        for j in row:
            neighbor[i] |= 1 << j
    complement_neighbor = [((1 << n) - 1) ^ neighbor[i] ^ (1 << i)
                           for i in range(n)]
    best = 0

    def search(chosen, available):
        nonlocal best
        if chosen + bin(available).count("1") <= best:
            return
        if not available:
            best = max(best, chosen)
            return
        while available and chosen + bin(available).count("1") > best:
            bit = available & -available
            i = bit.bit_length() - 1
            available ^= bit
            search(chosen + 1, available & complement_neighbor[i])

    search(0, (1 << n) - 1)
    return best


class JT913Tests(unittest.TestCase):
    def test_exact_instances(self):
        for n, expected_edges, expected_colors, expected_alpha in (
            (2, 0, 1, 2),
            (4, 3, 2, 3),
            (8, 1855, 14, 5),
        ):
            with self.subTest(n=n):
                k = n // 2
                data = instance(n, k, k - 1)
                self.assertEqual(verify_instance(data)["status"], "PASS")
                self.assertEqual(data["edge_count"], expected_edges)
                self.assertEqual(data["chromatic_number"], expected_colors)
                self.assertEqual(independence_number(data["adjacency"]), expected_alpha)

    def test_general_graph_rule(self):
        # K(5,2,1): edges join disjoint two-sets, the Petersen graph.
        data = instance(5, 2, 1)
        self.assertEqual(verify_instance(data)["status"], "PASS")
        self.assertEqual((data["vertex_count"], data["edge_count"]), (10, 15))
        self.assertNotIn("colors", data)


if __name__ == "__main__":
    unittest.main()
