import tkinter as tk
from tkinter import filedialog
from util.graph_spec import Vertex
import os

file_types = [("graph files","*.graph"),("all files","*.*")]

def read_graph(file_path=None):
    if file_path == None:
        root = tk.Tk()
        root.withdraw()
        file_path =  filedialog.askopenfilename(initialdir = os.getcwd(),title = "Select file",filetypes = file_types)

    graph_file = ""
    graph_file = open(file_path, "r").read()
    
    split_input = graph_file.split("\n")
    if split_input[0] != "POSITIONS":
        print("No POSITIONS in file")
        return
    elif not "EDGES" in split_input:
        print("No EDGES in file")
        return
    elif not "END" in split_input:
        print("No END in file")
        return

    vertices = []

    positions_end = split_input.index("EDGES")
    for i in range(1,positions_end):
        split_pair = split_input[i].split()
        if len(split_pair) != 2:
            print(str(split_pair) + " not inputted as tuple")
            return
        position = tuple([float(x) for x in split_pair])
        vertices.append(Vertex(position))

    edges_end = split_input.index("END")
    for i in range(positions_end+1,edges_end):
        split_pair = split_input[i].split()
        if len(split_pair) != 2:
            print(str(split_pair) + " not inputted as tuple")
            return
        u,v = tuple([int(x) for x in split_pair])
        vertices[u].add_edge(v)
        vertices[v].add_edge(u)

    return vertices

def write_graph(vertices,file_path=None):
    if file_path == None:
        root = tk.Tk()
        root.withdraw()
        file_path =  filedialog.asksaveasfilename(initialdir = os.getcwd(),title = "Select file",filetypes = file_types)

    split_name = file_path.split(".")
    if split_name[0] == "":
        return

    final_path_name = split_name[0] + ".graph"
    graph_file = open(final_path_name, "w+")
    
    positions = ""
    edges = ""
    for v, vertex in enumerate(vertices):
        positions += str(vertex.pos[0]) + " " + str(vertex.pos[1]) + "\n"
        for u in vertex:
            if v < u:
             edges += str(v) + " " + str(u) + "\n" 

    graph_file.write("POSITIONS\n")
    graph_file.write(positions)
    graph_file.write("EDGES\n")
    graph_file.write(edges)
    graph_file.write("END")
    graph_file.close()