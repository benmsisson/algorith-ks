from graphics.lib import *
from math import hypot
from random import randrange
import pyscreenshot as ImageGrab

#Returns true if the edge from u to v is directed
def is_directed(dir_G, u, v):
    return not u in dir_G[v]


def simple(vertices,graph_name="graph"):
    x_size, y_size = 0, 0
    for vertex in vertices:
        x_size = max(vertex.pos[0], x_size)
        y_size = max(vertex.pos[1], y_size)

    size_mod = 21
    x_offset = 0
    radius = 10
    assert size_mod / 2 > radius

    window = GraphWin(graph_name, x_offset + x_size * size_mod + 2 * radius,
                      y_size * size_mod + 2 * radius, False)
    for index in range(len(vertices)):  #Draw all the vertices
        if len(vertices[index]) != 0:
            c = Circle(vertices[index].circle_point(size_mod, radius,
                                                    x_offset), radius)

            t = Text(vertices[index].circle_point(size_mod, radius, x_offset),
                     index)
            t.draw(window)
            c.draw(window)
            for edgeIndex in range(len(vertices[index])):
                otherIndex = vertices[index][edgeIndex]
                if (index > otherIndex):
                    l = Line(vertices[index].circle_point(
                        size_mod, radius, x_offset),
                             vertices[otherIndex].circle_point(
                                 size_mod, radius, x_offset))
                    l.draw(window)

    window.getMouse()  # Pause to view result

def graph(rs, autoscroll, update_time, close_on_finish, reset_index, graph_name):
    if reset_index:
        for v in range(len(rs.vertices)):
            rs.indx[v] = v
        
    x_size, y_size = 0, 0
    for vertex in rs.vertices:
        x_size = max(vertex.pos[0], x_size)
        y_size = max(vertex.pos[1], y_size)

    size_mod = 12

    size_mod = 21
    radius = 10
    assert size_mod / 2 > radius

    x_offset_left = 0
    x_offset_right = 70

    title_offset = (65, 10)
    set_offset = (200, 22.5)
    alpha_offset = (40, 10)
    max_alpha_offset = (40, 60)
    alpha_descr_offset = (-90, -15)

    y_spacing_text = 15

    x_grid_size = x_size * size_mod + 2 * radius
    y_grid_size = y_size * size_mod + 2 * radius

    x_total = x_offset_left + x_grid_size + x_offset_right
    y_total = y_grid_size + -2 * alpha_descr_offset[1]

    window = GraphWin(graph_name, x_total, y_total, False)
    geom = window.master.geometry()
    w = geom.split("x")[0]
    r = geom.split("x")[1]
    h = r.split("+")[0]
    x1 = r.split("+")[1]
    y1 = r.split("+")[2]
    x1 = int(x1)
    y1 = int(y1)
    x2 = x1 + int(w)
    y2 = y1 + int(h) + 23

    lines = dict()
    nodes = dict()
    #Draw all the rs.vertices, store all of the nodes and edges we make
    for index in range(len(rs.vertices)):
        c = Circle(rs.vertices[index].circle_point(size_mod, radius,
                                                x_offset_left), radius)
        t = Text(rs.vertices[index].circle_point(size_mod, radius, x_offset_left),
                 rs.indx[index])
        nodes.update({index: c})
        c.setOutline("gray80")
        t.draw(window)
        c.draw(window)

        for edgeIndex in range(len(rs.vertices[index])):
            otherIndex = rs.vertices[index][edgeIndex]

            if (index >
                    otherIndex):  #We will always store the edges as a tuple, ordering by index
                l = Line(rs.vertices[index].circle_point(size_mod, radius,
                                                      x_offset_left),
                         rs.vertices[otherIndex].circle_point(
                             size_mod, radius, x_offset_left))
                l.setFill("gray80")
                l.setDash((10, 25))
                l.draw(window)
                lines.update({(index, otherIndex): l})

    #Set up our texts
    reassembly = Text(
        Point(title_offset[0], title_offset[1]), "Reassembly Order:")
    reassembly.setSize(13)
    # reassembly.draw(window) NOT DRAWING

    alpha = Text(
        Point(x_offset_left + x_grid_size + alpha_offset[0], alpha_offset[1]),
        u'\u03B1' + " Now:")
    alpha.setSize(13)
    alpha.draw(window)

    alpha_num = Text(
        Point(x_offset_left + x_grid_size + alpha_offset[0],
              alpha_offset[1] + y_spacing_text), "0")
    alpha_num.draw(window)

    max_alpha = Text(
        Point(x_offset_left + x_grid_size + max_alpha_offset[0],
              max_alpha_offset[1]), u'\u03B1' + " Max:")
    max_alpha.setSize(13)
    max_alpha.draw(window)

    max_alpha_num = Text(
        Point(x_offset_left + x_grid_size + max_alpha_offset[0],
              max_alpha_offset[1] + y_spacing_text), "0")
    max_alpha_num.draw(window)

    alpha_descr = Text(
        Point(x_total + alpha_descr_offset[0],
              y_total + alpha_descr_offset[1]), u'\u03B1' +
        " is the number of spliced edges\nin current (bolded) reassembly   ")
    alpha_descr.draw(window)

    texts = [None] * len(rs.Blst)
    max_current_history = [0] * len(rs.Blst)
    max_current_red = 0
    max_current_set = set([])

    max_total_history = [(0, set())] * len(rs.Blst)
    max_total_red = 0

    reassembly_width = 100


    #Now we begin our reassembly portion
    index = 0
    while True:
        update(update_time)
        key = "Right" if autoscroll else window.getKey()
        if key == "Right":
            # # # grab fullscreen
            # im = ImageGrab.grab(bbox=(x1,y1,x2,y2))

            # # # save image file
            # im.save('example_1/part_'+str(index+1)+'.png')

            # show image in a window
            # im.show()
            if index > len(rs.Blst):  #Done!
                if index + 1 == len(rs.Blst):
                    print("DONE")
                if close_on_finish:
                    break
                else:
                    pass
            elif index < len(rs.Blst):
                for up_to in range(index):  #Move everything down
                    texts[up_to].move(0, y_spacing_text)
                    texts[up_to].setStyle("normal")

                current = rs.Blst[index]
                n_str = "{"
                num_comma = 0
                for x_vert in current:  #This could be combined with the loop below, but it is separated for readability
                    n_str += str(rs.indx[x_vert]) + u'\u2003'
                n_str = n_str[0:-1]  #slice off last comma
                n_str += "}"

                n_str = n_str.ljust(50,"_")
                # n_str = n_str.replace("_",","+u'\u2007')

                t = Text(Point(200, set_offset[1]), n_str)
                t.setStyle("bold")
                # t.draw(window) NOT DRAWING
                texts[index] = t 

                current_red = 0
                for circle in nodes.values():
                    circle.setWidth(1)
                for x_vert in current:  #For every vertex in our current reassembly
                    circle = nodes[x_vert]
                    circle.setOutline("black")  #Repeat multiple times
                    circle.setWidth(2)
                    for y_vert in rs.vertices[x_vert]:
                        if y_vert in current:
                            if x_vert > y_vert:  #We only want to connect them if we are above them, and they are also reassembled
                                line = lines[(x_vert, y_vert)]
                                line.setDash(())
                                if is_directed(
                                        rs.dir_G, x_vert, y_vert
                                ):  #Check how the directed graph orders us
                                    line.setArrow("last")
                                elif is_directed(rs.dir_G, y_vert, x_vert):
                                    line.setArrow("first")
                                line.setFill("black")
                        else:  #Unconnected edge!
                            line = lines[(max(x_vert, y_vert), min(
                                x_vert, y_vert))]
                            line.setDash((10, 5))
                            line.setFill("Red")
                            current_red += 1
                if current_red > max_current_red or max_current_set.issubset(
                        current):
                    #If our current reassembly is a superset of the previous reassembly, we need to update our current red
                    max_current_red = current_red  #Even if our current red is less than the previous red
                    max_current_set = current
                    alpha_num.setText(current_red)
                if current_red > max_total_red:  #The same is not necessary for the max red
                    max_total_red = current_red
                    max_alpha_num.setText(current_red)
                current_index = min(len(rs.Blst) - 1, index + 1)
                max_total_history[current_index] = (max_total_red,
                                                    max_current_set)
                max_current_history[current_index] = max_current_red
            index += 1
        elif key == "Left":
            index -= 1
            if index == len(rs.Blst):
                pass
            elif index < 0:
                index = 0
            else:
                #Update our texts, using the history we saved
                max_current_red = max_current_history[index]
                alpha_num.setText(max_current_red)
                max_total_red, max_current_set = max_total_history[index]
                max_alpha_num.setText(max_total_red)
                reassembled = set()

                for Blst_index in range(index + 1):  #Move our texts back up
                    if Blst_index < index:
                        texts[Blst_index].move(0, -y_spacing_text)
                        reassembled = reassembled.union(
                            rs.Blst[Blst_index])
                        if Blst_index == index - 1:
                            texts[Blst_index].setStyle("bold")
                    else:
                        texts[Blst_index].undraw()
                        texts[Blst_index] = None

                current = rs.Blst[index]
                for circle in nodes.values():
                    circle.setWidth(1)
                for x_vert in current:
                    if x_vert in reassembled:  #If we are reassembled we may not need to do any work
                        for y_vert in rs.vertices[x_vert]:
                            paired_up = False
                            for Blst_index in range(
                                    index
                            ):  #Check to make sure if we have been previously connected
                                check_Blst = rs.Blst[Blst_index]
                                if y_vert in check_Blst and x_vert in check_Blst:
                                    paired_up = True
                                    break

                            if paired_up:  #If we, and the other edge we are connected to, are both reassembled, then nothing needs to be done
                                nodes[x_vert].setWidth(2)
                            else:  #Otherwise we must disconnected our edges
                                if x_vert > y_vert:
                                    line = lines[(x_vert, y_vert)]
                                else:
                                    line = lines[(y_vert, x_vert)]
                                line.setFill("Red")
                                line.setArrow("none")
                                line.setDash((10, 5))

                    else:  #Otherwise, if this was the first time we were reassembled
                        nodes[x_vert].setOutline("Gray80")
                        for y_vert in rs.vertices[x_vert]:
                            if x_vert > y_vert:  #Find ordering
                                line = lines[(x_vert, y_vert)]
                            else:
                                line = lines[(y_vert, x_vert)]

                            line.setArrow("none")
                            if y_vert in current:  #Make sure no one is connected to us
                                line.setFill("Red")
                                line.setDash((10, 5))
                            else:  #If both nodes were just dissasembled, we revert to gray
                                line.setFill("Gray80")
                                line.setDash((10, 25))
    print("Reassembly complete w/ max alpha =", max_alpha_num.getText())
