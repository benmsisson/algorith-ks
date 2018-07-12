from graphics.lib import *
from util.graph_spec import Vertex, check_one_three
from util.file_io import read_graph, write_graph
from algorithm.driver import start_reassembly

numButtons = 8
ADD_NODE = 0
DEL_NODE = 1
MOV_NODE = 2
ADD_EDGE = 3
DEL_EDGE = 4
OPN_GRPH = 5
FIN_GRPH = 6
SAV_GRPH = 7

windowWidth = 960
# windowWidth = 600
windowHeight = 600

buttonWidth = 25
buttonHeight = 20

toolbarWidth = (numButtons + 1) * buttonWidth
toolbarHeight = 105

gridWidth = windowWidth - 0
gridHeight = windowHeight - toolbarHeight

graphWidth = 0
graphHeight = 0
gridSize = 0
buttons = []
gridRect = None

errorText = None
errorRect = None


class GraphState:
    def __init__(self):
        self.nextVertex = 0
        self.mode = -1
        self.positionToVertex = dict()

        self.vertexToPosition = dict()
        self.vertexHasError = dict()

        self.edgesToLines = dict()
        self.vertices = []

    def reset(self):
        for c, _ in self.positionToVertex.values():
            c.undraw()
        for line in self.edgesToLines.values():
            line.undraw()

        self.nextVertex = 0
        self.mode = -1
        self.positionToVertex = dict()

        self.vertexToPosition = dict()
        self.vertexHasError = dict()

        self.edgesToLines = dict()
        self.vertices = []


def getMouseGridPos(mousePos):
    newX, newY = 0, 0
    baseX, baseY = mousePos.x - gridRect.p1.x, mousePos.y - gridRect.p1.y

    if baseX % gridSize < gridSize / 2:
        newX = int(baseX / gridSize) * gridSize
    else:
        newX = (int(baseX / gridSize) + 1) * gridSize
    if baseY % gridSize < gridSize / 2:
        newY = int(baseY / gridSize) * gridSize
    else:
        newY = (int(baseY / gridSize) + 1) * gridSize
    return Point(newX + gridRect.p1.x, newY + gridRect.p1.y)


def buttonFromIndex(win, index, row, rowSize, text):
    yPos = windowHeight - toolbarHeight * .75 + row * buttonHeight * 2.5
    xPos = windowWidth * (index + 1) / (rowSize + 1)
    topLeftPos = Point(xPos - buttonWidth, yPos - buttonHeight)
    bottomRightPos = Point(xPos + buttonWidth, yPos + buttonHeight)

    rect = Rectangle(topLeftPos, bottomRightPos)
    rect.draw(win)

    text = Text(
        Point((topLeftPos.x + bottomRightPos.x) / 2,
              (topLeftPos.y + bottomRightPos.y) / 2), text)
    text.draw(win)

    return rect


def selectAndGetPosition(v, state, win):
    c, _ = state.positionToVertex[state.vertexToPosition[v]]
    c.setFill("grey")
    secondPos = getMouseGridPos(win.getMouse())

    # If they fixed it, let them know by unhighlighting the vertex
    # However, do not alert them if they broke it until they try to reassemble
    if state.vertexHasError[v]:
        checkEdgeCount(v, state)
    if not state.vertexHasError[v]:
        c.setFill("black")
    else:
        c.setFill("red")
    return secondPos


def handleMouseClick(state, win):
    mousePos = win.getMouse()
    errorText.undraw()
    errorRect.undraw()
    gridMousePos = getMouseGridPos(mousePos)

    for i, b in enumerate(buttons):
        if pointInRect(mousePos, b):
            buttons[state.mode].setFill("white")
            state.mode = i
            if state.mode == OPN_GRPH:
                handleOpenGraph(state, win)
            elif state.mode == FIN_GRPH:
                handleFinGraph(state, win)
            elif state.mode == SAV_GRPH:
                handleSaveGraph(state, win)
            else:
                buttons[state.mode].setFill("grey")
            return
    else:
        if not pointInRect(gridMousePos, gridRect):
            return
    if state.mode == ADD_NODE:
        handleAddNode(gridMousePos, state, win)
    if state.mode == DEL_NODE:
        handleDelNode(gridMousePos, state, win)
    if state.mode == MOV_NODE:
        handleMovNode(gridMousePos, state, win)
    if state.mode == ADD_EDGE:
        handleAddEdge(gridMousePos, state, win)
    if state.mode == DEL_EDGE:
        handleDelEdge(gridMousePos, state, win)


def convertToVertices(state):
    vertices = []
    oldToNew = dict()
    nextNew = 0
    for v, edges in enumerate(state.vertices):
        if edges == -1:
            continue
        pos = state.vertexToPosition[v]
        newX = int(round((pos.x - gridRect.p1.x) / gridSize))
        newY = int(round((pos.y - gridRect.p1.y) / gridSize))
        vertices.append(Vertex((newX, newY)))
        oldToNew[v] = nextNew
        nextNew += 1

    for v, edges in enumerate(state.vertices):
        if edges == -1:
            continue
        nV = oldToNew[v]
        for u in edges:
            nU = oldToNew[u]
            vertices[nV].add_edge(nU)
    return vertices

def checkIntersection(state, uv, L1):
        for xy, L2 in state.edgesToLines.items():
            firstSame = (xy[0] == uv[0] or xy[0] == uv[1])
            secondSame = (xy[1] == uv[0] or xy[1] == uv[1])
            if firstSame or secondSame:
                continue
            if linesIntersect(L1, L2):
                L1.setFill("red")
                return True
        L1.setFill("black")
        return False

def checkAllIntersections(state):
    hasIntersection = False
    for uv, L1 in state.edgesToLines.items():
        result = checkIntersection(state, uv, L1)
        hasIntersection = hasIntersection
    return hasIntersection


def checkEdgeCount(v, state):
    if not v in state.vertexToPosition:
        return

    c, _ = state.positionToVertex[state.vertexToPosition[v]]
    if state.vertices[v] == -1:
        assert False
        return

    if len(state.vertices[v]) != 3 and len(state.vertices[v]) != 1:
        c.setFill("red")
        state.vertexHasError[v] = True
    else:
        c.setFill("black")
        state.vertexHasError[v] = False


def drawNodeCircle(mousePos, state, win, index):
    c = Circle(mousePos, gridSize / 3.5)
    c.draw(win)
    c.setFill("black")
    state.positionToVertex[mousePos] = (c, index)
    state.vertexToPosition[index] = mousePos


def createEdge(pos1, pos2, state, win, checkCross=True):
    c, v = state.positionToVertex[pos1]
    c2, u = state.positionToVertex[pos2]
    uv = (min(u, v), max(u, v))

    if uv in state.edgesToLines:
        return

    state.vertices[v].append(u)
    state.vertices[u].append(v)
    l = Line(pos1, pos2)
    l.draw(win)
    state.edgesToLines[uv] = l

    if checkCross:
        checkIntersection(state,uv,l)


def handleAddNode(mousePos, state, win):
    if mousePos in state.positionToVertex:
        return
    v = state.nextVertex
    drawNodeCircle(mousePos, state, win, v)
    state.vertexHasError[v] = False
    state.vertices.append([])
    state.nextVertex += 1


def handleDelNode(mousePos, state, win):
    if not mousePos in state.positionToVertex:
        return
    c, v = state.positionToVertex[mousePos]
    c.undraw()
    # We will parse out all these later on. Just easier to leave the blank and pretend it never happened
    state.vertices[v] = -1
    del state.positionToVertex[mousePos]
    del state.vertexToPosition[v]
    del state.vertexHasError[v]

    for u, edgesList in enumerate(state.vertices):
        if edgesList == -1:
            continue
        if v in edgesList:
            edgesList.remove(v)
            uv = (min(u, v), max(u, v))
            state.edgesToLines[uv].undraw()
            del state.edgesToLines[uv]

    checkAllIntersections(state)


def handleMovNode(mousePos, state, win):
    if not mousePos in state.positionToVertex:
        return
    c, v = state.positionToVertex[mousePos]
    secondPos = selectAndGetPosition(v, state, win)

    if not pointInRect(secondPos,
                       gridRect) or secondPos in state.positionToVertex:
        return

    del state.positionToVertex[mousePos]
    c.undraw()
    state.vertexToPosition[v] = secondPos
    drawNodeCircle(secondPos, state, win, v)

    for u in state.vertices[v]:
        uv = (min(u, v), max(u, v))
        state.edgesToLines[uv].undraw()
        uPos = state.vertexToPosition[u]
        state.edgesToLines[uv] = Line(secondPos, uPos)
        state.edgesToLines[uv].draw(win)

    checkAllIntersections(state)


def handleAddEdge(mousePos, state, win):
    if not mousePos in state.positionToVertex:
        return

    c, v = state.positionToVertex[mousePos]
    secondPos = selectAndGetPosition(v, state, win)

    if not secondPos in state.positionToVertex or mousePos == secondPos:
        return

    createEdge(mousePos, secondPos, state, win)


def handleDelEdge(mousePos, state, win):
    if not mousePos in state.positionToVertex:
        return

    c, v = state.positionToVertex[mousePos]
    secondPos = selectAndGetPosition(v, state, win)

    if not secondPos in state.positionToVertex:
        return

    c2, u = state.positionToVertex[secondPos]
    uv = (min(u, v), max(u, v))

    if not uv in state.edgesToLines:
        return

    state.edgesToLines[uv].undraw()
    del state.edgesToLines[uv]
    state.vertices[v].remove(u)
    state.vertices[u].remove(v)

    checkAllIntersections(state)


def handleFinGraph(state, win):
    vertices = convertToVertices(state)
    if len(vertices) == 0:
        return

    for v in range(len(vertices)):
        checkEdgeCount(v, state)

    valid = not checkAllIntersections(state) and check_one_three(vertices)

    if not valid:
        errorRect.draw(win)
        errorText.draw(win)
        return

    start_reassembly(vertices,"builder")


def handleOpenGraph(state, win):
    def convertPosition(xy):
        newX = (xy[0] * gridSize) + gridRect.p1.x
        newY = (xy[1] * gridSize) + gridRect.p1.y
        return Point(newX, newY)

    vertices = read_graph()
    if vertices == None:
        return

    state.reset()

    for vertex in vertices:
        handleAddNode(convertPosition(vertex.pos), state, win)

    for v, vertex in enumerate(vertices):
        for u in vertex:
            if v < u:
                pos1 = convertPosition(vertex.pos)
                pos2 = convertPosition(vertices[u].pos)
                createEdge(pos1, pos2, state, win, False)
    checkAllIntersections(state)


def handleSaveGraph(state, win):
    vertices = convertToVertices(state)
    write_graph(vertices)


def buildGraph(width, height):
    global graphWidth, graphHeight, buttons, gridSize, gridRect, errorText, errorRect

    win = GraphWin("Graph Builder", windowWidth, windowHeight, autoflush=False)
    state = GraphState()

    gridSize = 0
    xOffset, yOffset = 0, 0
    if gridWidth / width < gridHeight / height:
        gridSize = gridWidth / width
    else:
        gridSize = gridHeight / height
        xOffset = (gridWidth - gridSize * width) / 2

    graphWidth = width * gridSize
    graphHeight = height * gridSize

    for x in range(width + 1):
        xPos = xOffset + x * gridSize
        l = Line(Point(xPos, yOffset), Point(xPos, graphHeight + yOffset))
        l.setDash((2, 1))
        l.draw(win)
    for y in range(height + 1):
        yPos = yOffset + y * gridSize
        l = Line(Point(xOffset, yPos), Point(graphWidth + xOffset, yPos))
        l.setDash((2, 1))
        l.draw(win)

    gridRect = Rectangle(
        Point(xOffset, yOffset),
        Point(xOffset + width * gridSize, yOffset + height * gridSize))

    buttons = [0] * numButtons
    numInFirstRow = 5
    numInSecondRow = 3
    buttons[ADD_NODE] = buttonFromIndex(win, ADD_NODE, 0, numInFirstRow,
                                        "Add\nNode")
    buttons[DEL_NODE] = buttonFromIndex(win, DEL_NODE, 0, numInFirstRow,
                                        "Delete\nNode")
    buttons[MOV_NODE] = buttonFromIndex(win, MOV_NODE, 0, numInFirstRow,
                                        "Move\nNode")
    buttons[ADD_EDGE] = buttonFromIndex(win, ADD_EDGE, 0, numInFirstRow,
                                        "Add\nEdge")
    buttons[DEL_EDGE] = buttonFromIndex(win, DEL_EDGE, 0, numInFirstRow,
                                        "Delete\nEdge")

    buttons[OPN_GRPH] = buttonFromIndex(win, OPN_GRPH - numInFirstRow, 1,
                                        numInSecondRow, "Open\nGraph")
    buttons[FIN_GRPH] = buttonFromIndex(win, FIN_GRPH - numInFirstRow, 1,
                                        numInSecondRow, "Assemble\nGraph")
    buttons[SAV_GRPH] = buttonFromIndex(win, SAV_GRPH - numInFirstRow, 1,
                                        numInSecondRow, "Save\nGraph")
    state.mode = 0
    buttons[0].setFill("grey")

    xMid = (gridRect.p1.x + gridRect.p2.x) / 2
    yMid = (gridRect.p1.y + gridRect.p2.y) / 2
    textWidth = 160
    textHeight = 30
    textSize = 14

    textPos = Point(xMid, yMid + textHeight / 2)

    topLeftPos = Point(xMid - textWidth / 2, yMid)
    bottomRightPos = Point(xMid + textWidth / 2, yMid + textHeight)

    # Neither of these are drawn right now, but are set up for later
    errorRect = Rectangle(topLeftPos, bottomRightPos)
    errorRect.setFill("white")

    errorText = Text(textPos, "Not planar a 1-3 cactus")
    errorText.setFill("red")
    errorText.setSize(textSize)

    while True:
        handleMouseClick(state, win)


buildGraph(73, 38)
