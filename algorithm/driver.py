from copy import deepcopy
from algorithm.reassemble import algorithmKS
from algorithm.preprocess import start_phase
import graphics.draw as draw
from util.reassembly_state import ReassemblyState
from util.graph_spec import *


# It may be possible to remove space surrounding the graph in order to have it
# fit the screen more easily.
def crop_graph(vertices):
    min_x, min_y = 2**16, 2**16
    max_x, max_y = 0, 0
    for vertex in vertices:
        min_x = min(vertex.pos[0], min_x)
        min_y = min(vertex.pos[1], min_y)
        max_x = max(vertex.pos[0], max_x)
        max_y = max(vertex.pos[1], max_y)

    max_x = max_x - min_x
    max_y = max_y - min_y

    for v, vertex in enumerate(vertices):
        vertex.pos = (vertex.pos[0] - min_x, vertex.pos[1] - min_y)


def start_reassembly(vertices, graph_name):
    if not check_one_three(vertices):
        return

    blank_verts = [0] * len(vertices)
    crop_graph(vertices)
    for v, vertex in enumerate(vertices):
        blank_verts[v] = Vertex(vertex.pos)

    print(graph_name)
    draw.simple(vertices, graph_name=graph_name)
    preprocess_vertices = deepcopy(vertices)
    planarity, layer_states = start_phase(preprocess_vertices, blank_verts)
    rs = ReassemblyState(vertices, planarity)
    algorithmKS(layer_states, rs, planarity, True)
    draw.graph(rs=rs,autoscroll=False,update_time=30,close_on_finish=True,reset_index=False,graph_name=graph_name)
    