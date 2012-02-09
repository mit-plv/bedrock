#!/usr/bin/python
import sys

class Graph:
    def __init__(self):
        self._edges = {}
    
    def edge(self, st, en, lbl):
        if not self._edges.has_key(st):
            self._edges[st] = {}
        self._edges[st][en] = lbl

    def edges(self, st):
        if self._edges.has_key(st):
            return self._edges[st]
        return {}

    def nodes(self):
        return self._edges.keys()

class CycleFound (Exception):
    def __init__(self, path, labels):
        self.path = path
        self.labels = labels

def find_cycle(gr):
    visited = set([])
    remaining = set(gr.nodes())   
    
    while len(remaining) > 0:
        root = remaining.pop()
        lvisit = set([root])
        path = []
        labels = []

        def find_strict_cycle(st):
            if st in path:
                f = path.index(st)
                if '<' in labels[f:]:
                    raise CycleFound(path[f:] + [st], labels[f:])
            if st in visited:
                return None
            
            path.append(st)
            visited.add(st)
            for (to, lbl) in gr.edges(st).items():
                labels.append(lbl)
                find_strict_cycle(to)
                labels.pop()
            path.pop()
                
            return None

        try:
            find_strict_cycle(root)
        except CycleFound, e:
            return (e.path, e.labels)
        
    return None

def read_graph(file):
    lines = file.readlines()

    gr = Graph()
    last = None
    for ln in lines:
        ln = ln.replace(';', '')
        parts = ln.split()
        if len(parts) == 3:
            last = parts[0]
        elif len(parts) == 2:
            parts = [last, parts[0], parts[1]]
        else:
            assert False

        st = parts[0]
        en = parts[2]
        gr.edge(st, en, parts[1])

    return gr

if __name__ == '__main__':
    gr = read_graph(sys.stdin)
    res = find_cycle(gr)
    if res is None:
        print "No cycle found"
    else:
        print "Cycle found!"
        (nodes, labels) = res
        l = len(labels)
        for i in range(0, l):
            print "%s %s " % (nodes[i], labels[i]) ,
        print nodes[l]
