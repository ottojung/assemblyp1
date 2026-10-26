import itertools

def rigid(support_edges, mult):
    # support_edges: list of (u,v); mult: dict edge->int (true mult)
    # decider: existence of nonzero integer delta on support edges with
    #   incidence*delta=0, sum(delta)=0, mult[e]+delta[e]>=1 for all e.
    n = len(support_edges)
    # vertices
    verts = sorted(set([u for u,v in support_edges]+[v for u,v in support_edges]))
    idx = {v:i for i,v in enumerate(verts)}
    # incidence matrix rows: vertices, cols edges; delta inflow-outflow? use out-in
    # constraint: for each vertex, sum delta on outgoing - sum delta on incoming = 0
    # plus sum delta =0 (redundant if connected but keep)
    # brute force small range
    R=3
    for deltas in itertools.product(range(-R,R+1), repeat=n):
        if all(d==0 for d in deltas): continue
        # multiplicity constraint
        ok=True
        for i,e in enumerate(support_edges):
            if mult[e]+deltas[i] < 1: ok=False; break
        if not ok: continue
        # incidence
        flow=[0]*len(verts)
        for i,(u,v) in enumerate(support_edges):
            flow[idx[u]] += deltas[i]
            flow[idx[v]] -= deltas[i]
        if any(x!=0 for x in flow): continue
        if sum(deltas)!=0: continue
        return False  # nontrivial circulation exists => not rigid
    return True

if __name__=="__main__":
    # cycle example
    edges=[(0,1),(1,2),(2,0)]
    mult={(0,1):1,(1,2):1,(2,0):1}
    print("cycle rigid:", rigid(edges,mult))
    # theta non-rigid
    edges2=[(0,1),(0,1),(1,2)]  # parallel support collapsed? treat as one support edge mult 2
    edges2=[(0,1),(1,2)]
    mult2={(0,1):2,(1,2):1}
    print("theta-ish:", rigid(edges2,mult2))
