from math import atan2, pi
from graphics.lib import Point


class Vertex:
    def __init__(self, pos):
        self.pos = pos
        self.edges = []
        self.is_circle = True

    def __str__(self):
        return str(self.pos) + str(self.edges)

    def __len__(self):
        return len(self.edges)

    def __setitem__(self, key, value):
        self.edges[key] = value

    def __getitem__(self, key):
        return self.edges[key]

    def __eq__(self, other):
        if self.pos!=other.pos:
            return False
        if len(self.edges) != len(other.edges):
            return False
        for v in range(len(self.edges)):
            if self.edges[v] != other.edges[v]:
                return False
        return True

    def __contains__(self, item):
        return item in self.edges

    def add_edge(self, connect_to):
        self.edges.append(connect_to)

    def remove_edge(self, remove_to):
        self.edges.remove(remove_to)

    def circle_point(self, sizeMod, radius, x_offset):
        x, y = self.pos
        return Point(x * sizeMod + radius + x_offset, y * sizeMod + radius)


# to_consider is a set or a list of ints, not of vertices
def upper_left_most(vertices, to_consider=None, only_deg_1=True):
    to_return = -1
    # Initialize our right and down coordinates to arbitrary large numbers
    tr_x, tr_y = 2**16, 2**16
    if to_consider == None:
        to_consider = range(len(vertices))
    for v in to_consider:
        # Filter out items in the to_consider if necessary
        if only_deg_1:
            if len(vertices[v]) != 1:
                continue
        else:
            if len(vertices[v]) == 0:
                continue

        n_x, n_y = vertices[v].pos
        # If we are above them, we are always better
        if n_y < tr_y:
            to_return = v
            tr_x, tr_y = vertices[v].pos
        elif n_y == tr_y:
            # Otherwise, if we are at the same height, pick the leftmost one
            if n_x < tr_x:
                to_return = v
                tr_x, tr_y = vertices[v].pos
    if to_return == -1:
        # If we haven't found anything, redo this whole thing
        # But try accept to_consider of other degrees as valid
        if only_deg_1:
            return upper_left_most(vertices, to_consider, False)
        else:
            return -1
    return to_return


def outer_face(vertices, start):
    def angle_from_twelve(x, y):
        return (pi / 2 - atan2(y, x) + 2 * pi) % (2 * pi)

    def angle_delta(from_pos, to_pos):
        # Our coordinate system has the bottom left as (0,height), so flip the y here
        return angle_from_twelve(to_pos[0] - from_pos[0],
                                 from_pos[1] - to_pos[1])

    def make_angle_above(base, angle):
        if angle < base:
            return 2 * pi + angle
        else:
            return angle

    path = []
    unique_path = []
    # Initialize every vertex such that all vertices are unmarked
    visited = set()
    edges_traversed = set()
    total_edges_traversed = []

    last_angle = 0
    last = -1
    current = start

    x = 0
    #While the graph has edges left unmarked, starting at the upper leftmost unmarked vertex, traverse the graph by taking the next clockwise edge at each vertex encountered, marking each time a vertex is visited, until the traversal returns to the original vertex.
    while True:
        x += 1
        # This should never be raised, but I have this here so we know.
        # This signals an error with the embedding, or the start position
        assert x < len(vertices) * 2

        # Starting at the upper leftmost unmarked vertex,
        # traverse the graph by taking the next clockwise edge at each vertex encountered.

        path.append(current)
        if not current in visited:
            unique_path.append(current)
        visited.add(current)

        possible = [v for v in vertices[current].edges if not v == last]
        if len(possible) == 0:
            next = last
        else:
            angles_to = [
                angle_delta(vertices[current].pos, vertices[v].pos)
                for v in possible
            ]
            corrected_angles = [
                make_angle_above(last_angle, angle) for angle in angles_to
            ]
            next = possible[corrected_angles.index(min(corrected_angles))]

        edge = (min(current, next), max(current, next))
        edges_traversed.add(edge)
        total_edges_traversed.append(edge)
        last_angle = angle_delta(vertices[next].pos, vertices[current].pos)
        last = current
        current = next

        if current == start:
            break
    return path, edges_traversed, total_edges_traversed


def check_one_three(vertices):
    isValid = True
    for v, vertex in enumerate(vertices):
        if len(vertex) != 1 and len(vertex) != 3:
            print("Vertex " + str(v) + " is invalid: " + str(vertex.edges))
            isValid = False
    return isValid
