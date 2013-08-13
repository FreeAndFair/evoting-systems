def components(graph):
    """
    Finds the connected-components of the input graph, using DFS.
    Input:
        dict graph: {obj node: list neighbors}
    Output:
        List of lists of nodes, where each sub-list represents one
        connected-component.
    """
    def dfsgraph(n):
        seen = {}
        stack = [n]
        while stack != []:
            vertex = stack.pop()
            if vertex in seen: continue
            seen[vertex] = True
            stack += graph[vertex]
        return seen.keys()
        
    sofar = {}
    comp = []
    for node in graph:
        if node not in sofar:
            lst = dfsgraph(node)
            comp.append(lst)
            for n in lst:
                sofar[n] = True
    return comp
