"""
A module to perform Graph Colouring.
"""
from collections import deque
import sys, pdb, traceback

class Graph(object):
    def __init__(self, nodes):
        pass
    def add(self, node):
        pass
    def remove(self, node):
        pass

class AdjListGraph(Graph):
    """ Is an undirected graph """
    def __init__(self, nodes=None):
        self.nodes = list(nodes) if nodes != None else []
        # dict self.adjlist: maps {int id: set([id, ...])}
        self.adjlist, self.node2id = self.generate_adj_list(nodes)
        
    def generate_adj_list(self, nodes):
        n = len(nodes)
        adjlst = {} # maps {int id: [int, ...]}
        node2id = {}
        for i, node in enumerate(nodes):
            node2id[node] = i
            adjlst[node2id[node]] = set()
        for node in nodes:
            for neighbor in node.neighbors:
                adjlst.setdefault(node2id[node], set()).add(node2id[neighbor])
        return adjlst, node2id

    def add(self, node):
        """ Does nothing if NODE already exists in graph. Also, updates
        Node neighbors of new and old nodes.
        """
        if node in self.nodes: return
        if node not in self.node2id:
            self.node2id[node] = max(self.node2id.values()) + 1
        self.nodes.append(node)
        self.adjlist.setdefault(self.node2id[node], set())
        for neighbor in node.neighbors[:]:
            self.add(neighbor) # won't add duplicates
            node.add_neighbor(neighbor)
            self.adjlist[self.node2id[neighbor]].add(self.node2id[node])
            self.adjlist[self.node2id[node]].add(self.node2id[neighbor])
    
    def remove(self, node):
        """ Does nothing if NODE doesn't exist in graph. Also, updates
        Node neighbors of input NODE, as well as neighbors of NODE.
        """
        if node not in self.nodes: return
        rm_id = self.node2id[node]
        self.adjlist.pop(rm_id)
        self.nodes.remove(node)
        for neighbor in node.neighbors[:]:
            self.adjlist[self.node2id[neighbor]].remove(rm_id)
            node.remove_neighbor(neighbor)

    def __repr__(self):
        return "AdjListGraph({0} nodes)".format(len(self.nodes))
    def __str__(self):
        return self.__repr__()

class AdjMatGraph(Graph):
    """
    An Undirected Graph implemented with an adjacency matrix.
    NOT COMPLETE
    """
    def __init__(self, nodes):
        self.nodes = nodes
        self.mat, self.node2id = self.generate_adj_mat(nodes) # [[bool bool, ...], [bool bool, ...], ...]
        
    def generate_adj_mat(self, nodes):
        """ Generates adjacency matrix from input NODES. """
        n = len(nodes)
        mat = [[False for _ in xrange(n)] for _ in xrange(n)]
        node2id = {}
        for i, node in enumerate(nodes):
            node2id[node] = i
        for node in nodes:
            for neighbor in node.neighbors:
                mat[node2id[node]][node2id[neighbor]] = True
        return mat, node2id

    def __repr__(self):
        return "AdjMatGraph({0} nodes)".format(len(self.nodes))

class Node(object):
    """ Assumes the graph is undirected. """
    def __init__(self, val, neighbors=None):
        self.val = val
        self.neighbors = neighbors if neighbors != None else []
    def add_neighbor(self, node):
        if node not in self.neighbors:
            self.neighbors.append(node)
        if self not in node.neighbors:
            node.neighbors.append(self)
    def remove_neighbor(self, node):
        self.neighbors.remove(node)
        node.neighbors.remove(self)
                        
    def __eq__(self, o):
        return o and isinstance(o, Node) and o.val == self.val
    def __repr__(self):
        return "Node({0})".format(self.val)
    def __str__(self):
        return self.__repr__()

def graphcolour(graph, colours=("R", "G", "B", "Y", "M")):
    """ Outputs the colouring of the input graph. If no such possible
    colouring exists, then outputs None.
    """
    def is_done(state):
        """ Output True if this is a valid five-colouring """
        if None in [t[1] for t in state]:
            return False
        for node, colour in state:
            history = set()
            for neighbor in node.neighbors:
                if neighbor in history: continue
                neighbor_colour = [c for (n,c) in state if n == neighbor][0]
                history.add(neighbor)
                if colour == neighbor_colour:
                    return False
        return True
    def expand_state(state):
        """ Only expand out a single unassigned variable at a time. """
        for node, colour in state:
            if colour == None:
                out_states = []
                for new_colour in colours:
                    out_state = []
                    for (n, c) in state:
                        if n == node:
                            out_state.append((n, new_colour))
                        else:
                            out_state.append((n, c))
                    out_states.append(tuple(out_state))
                return out_states
        return None
    def make_colouring(state):
        return dict(state)
    stack = deque()
    history = set()
    initial_state = tuple([(node, None) for node in graph.nodes])
    stack.appendleft(initial_state)
    while stack:
        cur_state = stack.popleft()
        if cur_state in history:
            continue
        history.add(cur_state)
        if is_done(cur_state):
            return make_colouring(cur_state)
        new_states = expand_state(cur_state)
        if new_states != None:
            stack.extendleft(new_states)
    print "Couldn't find solution."
    return None

def fivecolour_planar(graph, colours=("R","G","B","Y","M")):
    """
    Input:
        Graph GRAPH:
            Input graph must be a planar graph.
        tuple COLOURS:
            This can be a list/tuple of ANY five elements. To fivecolour,
            ints/strings/objects are valid colours.
        list REMOVED: 
            Used for the recursive procedure.
    Output:
        dict COLOURING: maps {Node node: obj COLOUR}
    """
    # Note: This isn't fully tested - but it's not going to get used
    #       anyways, so...
    # Implements linear-time algorithm from:
    #    http://www.devx.com/dotnet/Article/32927/0/page/2
    def get_available_colour(colouring, node):
        occupied_clrs = set()
        for neighbor in node.neighbors:
            clr = colouring.get(neighbor, None)
            if clr != None:
                occupied_clrs.add(clr)
        chosen_clr = tuple(set.difference(set(colours), occupied_clrs))[0]
        return chosen_clr
    if len(graph.nodes) == 1:
        return {graph.nodes[0]: colours[0]}
    removed_node = check_rule1(graph)
    if removed_node:
        old_neighbors = removed_node.neighbors[:]
        graph.remove(removed_node)
        colouring = fivecolour_planar(graph, colours=colours)
        for neighbor in old_neighbors:
            removed_node.add_neighbor(neighbor)
        graph.add(removed_node)
        colouring[removed_node] = get_available_colour(colouring, removed_node)
        return colouring
    X, N1, N2 = check_rule2(graph)
    if X:
        X_neighbors = X.neighbors[:]
        N1_neighbors, N2_neighbors = N1.neighbors[:], N2.neighbors[:]
        graph.remove(X); graph.remove(N1); graph.remove(N2);
        newnode = Node((N1.val, N2.val), N1.neighbors + N2.neighbors)
        graph.add(newnode)
        colouring = fivecolour_planar(graph, colours=colours)
        colour = colouring.pop(newnode)
        colouring[N1] = colour
        colouring[N2] = colour
        graph.add(N1)
        for neighbor in N1_neighbors:
            N1.add_neighbor(neighbor)
        graph.add(N2)
        for neighbor in N2_neighbors:
            N2.add_neighbor(neighbor)
        graph.add(X)
        for neighbor in X_neighbors:
            X.add_neighbor(neighbor)
        colouring[X] = get_available_colour(colouring, X)
        return colouring
    print "Error: Input Graph is not planar."
    return None
        
def check_rule1(graph):        
    for node in graph.nodes:
        if degree(node) < 5:
            return node
    return None

def check_rule2(graph):
    for node in [n for n in graph.nodes if degree(n) == 5]:
        NS = [n for n in node.neighbors if degree(n) <= 7]
        for i, n0 in enumerate(NS):
            for j, n1 in enumerate(NS):
                if i == j: continue
                if n0 not in n1.neighbors:
                    return node, n0, n1
    return None, None, None

def degree(node):
    return len(node.neighbors)

#### Graphs for Testing ####

def test_graph0():
    return make_full_graph(('A', 'B', 'C', 'D'))
def test_graph1():
    return make_full_graph(('A', 'B', 'C', 'D', 'E'))
def test_graph2():
    return make_full_graph(('A', 'B', 'C', 'D', 'E', 'F'))
def test_graph_island():
    a = Node("A"); a_0 = Node("A_0")
    b = Node("B"); b_0 = Node("B_0")
    c = Node("C"); d = Node("D")
    a.add_neighbor(a_0)
    a.add_neighbor(c)
    b.add_neighbor(c)
    b.add_neighbor(b_0)
    return AdjListGraph((a, a_0, b, b_0, c, d))
def make_full_graph(vals):
    nodes = [Node(x) for x in vals]
    for i, n0 in enumerate(nodes):
        for j, n1 in enumerate(nodes):
            if i == j: continue
            n0.add_neighbor(n1)
    return AdjListGraph(nodes)

def test_fivecolour_planar():
    g0 = test_graph0()
    g1 = test_graph1()
    g2 = test_graph2()
    g_island = test_graph_island()

    colouring0 = fivecolour_planar(g0)
    print "colouring0:", colouring0
    colouring1 = fivecolour_planar(g1)
    print "colouring1:", colouring1
    colouring2 = fivecolour_planar(g2)
    print "colouring2:", colouring2
    colouring_island = fivecolour_planar(g_island)
    print "colouring_island:", colouring_island

def test_fivecolour():
    g0 = test_graph0()
    g1 = test_graph1()
    g2 = test_graph2()
    g_island = test_graph_island()

    colouring0 = graphcolour(g0)
    print "colouring0:", colouring0
    colouring1 = graphcolour(g1)
    print "colouring1:", colouring1
    colouring2 = graphcolour(g2)
    print "colouring2:", colouring2
    colouring_island = graphcolour(g_island)
    print "colouring_island:", colouring_island

def main():
    #test_fivecolour_planar()
    test_fivecolour()

if __name__ == '__main__':
    main()
