from collections import deque
from copy import deepcopy


class ReassemblyState(object):
    def __init__(self, vertices, planarity):
        self.vertices = vertices

        self.super_in = [0] * len(vertices)
        for v in range(len(vertices)):
            self.super_in[v] = frozenset([v])

        self.dir_G = deepcopy(vertices)
        self.collapsed = set()

        self.indx = dict()
        self.total_i = 0
        self.vertex_to_super_out = dict()

        self.operations = []
        self.collapsed_by_cycle = []
        self.tree_has_collapsed = []
        self.tree_has_merged = []
        self.tree_will_collapse = []
        self.tree_to_super_out = []

        self.vertex_to_target = dict()

        # At each E-outerplanarity level in the graph ,define a queue that holds trees to be collapsed and merged.
        # Also, define dictionaries that map trees to various reassembly data about that.

        for layer in range(planarity):
            self.operations.append(deque())
            self.collapsed_by_cycle.append(dict())
            self.tree_has_collapsed.append(dict())
            self.tree_has_merged.append(dict())
            self.tree_will_collapse.append(set())
            self.tree_to_super_out.append(dict())

        self.re_list = [0] * (2 * len(self.vertices) - 1)
        self.re_index = 0

    def super_append(self, v):
        # Should be a set consisiting of v where v is a vertex
        assert len(v) == 1
        self.re_list[self.re_index] = v
        self.re_index += 1
        return self.re_index - 1

    def circle_plus(self, v, u):
        self.re_list[self.re_index] = (v, u)
        self.re_index += 1
        return self.re_index - 1

    def update_indx(self, indx):
        n_i = self.total_i
        for v, i in indx.items():
            self.indx[v] = i + self.total_i
            n_i += 1
        self.total_i = n_i

    def direct_edge(self, u, v):
        if u in self.dir_G[v]:
            self.dir_G[v].remove_edge(u)

    def merge_vertex_to_super_out(self, v, super_v):
        if v in self.collapsed:
            assert v in self.vertex_to_target
            u = self.vertex_to_target[v]
            if u in self.vertex_to_super_out:
                self.vertex_to_super_out[u] = self.circle_plus(
                    self.vertex_to_super_out[u], super_v)
            else:
                self.super_in[u] = self.circle_plus(self.super_in[u], super_v)
            return
        new_super = self.circle_plus(self.vertex_to_super_out[v], super_v)
        self.vertex_to_super_out[v] = new_super

    def merge_to_super_in(self, v, super_v):
        Bval = self.super_append(self.super_in[v])
        new_super = self.circle_plus(Bval, super_v)
        self.super_in[v] = new_super

    def build_Blst(self):
        self.Blst = [0] * len(self.re_list)
        for i, v in enumerate(self.re_list):
            if i >= self.re_index:
                return
            if len(v) == 1:
                self.Blst[i] = v
            else:
                u, v = v
                self.Blst[i] = self.Blst[u].union(self.Blst[v])
