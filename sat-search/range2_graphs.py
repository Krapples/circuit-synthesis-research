"""Enumerate L-meta-519 range-2 graphs: connected, max degree <= 3, every cycle of length >= 7,
with two ADJACENT vertices of degree 3. Up to isomorphism, n from 6 to NMAX.
Every connected graph is a spanning tree plus (cyclomatic number) extra edges; for n <= 11 and girth >= 7
the cyclomatic number is at most 2 (two cycles of length >= 7 need >= 10 vertices), so trees + 0..2 edges
covers the class. Writes range2_graphs.json: [{n, edges, E, tau, bound}] sorted by n, then E."""
import itertools, json, sys
import networkx as nx

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10


def cover_number(G):
    nodes = list(G.nodes)
    for k in range(len(nodes) + 1):
        for T in itertools.combinations(nodes, k):
            s = set(T)
            if all(u in s or v in s for u, v in G.edges):
                return k


def ok(G):
    if max(d for _, d in G.degree) > 3:
        return False
    g = nx.girth(G)
    if g != float('inf') and g < 7:
        return False
    return any(G.degree[u] == 3 and G.degree[v] == 3 for u, v in G.edges)


def main():
    out = []
    for n in range(6, NMAX + 1):
        seen = {}
        for T in nx.nonisomorphic_trees(n):
            if max(d for _, d in T.degree) > 3:
                continue
            non = [e for e in itertools.combinations(range(n), 2) if not T.has_edge(*e)]
            for extra in itertools.chain([()], ((e,) for e in non), itertools.combinations(non, 2)):
                G = T.copy(); G.add_edges_from(extra)
                if not ok(G):
                    continue
                h = nx.weisfeiler_lehman_graph_hash(G)
                bucket = seen.setdefault(h, [])
                if any(nx.is_isomorphic(G, H) for H in bucket):
                    continue
                bucket.append(G)
        graphs = [G for b in seen.values() for G in b]
        for G in graphs:
            E = G.number_of_edges(); tau = cover_number(G)
            out.append(dict(n=n, edges=sorted(tuple(sorted(e)) for e in G.edges), E=E, tau=tau, bound=E + tau - 1,
                            cycles=E - n + 1))
        print(f'n={n}: {len(graphs)} graphs (trees {sum(1 for G in graphs if G.number_of_edges() == n - 1)})', flush=True)
    out.sort(key=lambda d: (d['n'], d['E'], d['edges']))
    json.dump(out, open('range2_graphs.json', 'w'), indent=0)
    print(f'total {len(out)} graphs written to range2_graphs.json')


if __name__ == '__main__':
    main()
