"""Exact candidate witnesses for the existing rooted catalogue; NOT a Lean proof.

Each leaf insertion is assigned to an original catalogue representative by a
full root-preserving vertex bijection. All ordered adjacency pairs are checked.
The existing CanonicalTreeCoverage.step_sound/actual_tree_covered lemmas still
require Lean kernel checks of these witnesses before completeness is claimed.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re

SOURCE_SHA256 = '4e212d206794c94ef765e7f66513ef3cf6a6f41d18490efc3fcb23254adce33f'
WITNESS_SHA256 = 'c344d712c2478851a0ac518af24b88378fee68aff085dccc6628bf126cafad7e'
EXPECTED_SIZES = [1,1,2,4,9,20,48,115,286,719,1842]


def need(condition, message):
    if not condition:
        raise ValueError(message)


class FamilyParser:
    def __init__(self, text):
        self.tokens = re.findall(r'some|none|[()[\],]', text)
        need(''.join(self.tokens) == re.sub(r'\s', '', text), 'Unsupported catalogue syntax')
        self.i = 0

    def pop(self, expected=None):
        token = self.tokens[self.i]
        self.i += 1
        need(expected is None or token == expected, 'Unexpected token')
        return token

    def parse(self):
        token = self.pop()
        if token == 'none':
            return None
        if token == 'some':
            return ('some', self.parse())
        if token == '[':
            items = []
            while self.tokens[self.i] != ']':
                items.append(self.parse())
                if self.tokens[self.i] == ',':
                    self.pop(',')
                else:
                    break
            self.pop(']')
            return items
        need(token == '(', 'Unexpected expression')
        if self.tokens[self.i] == ')':
            self.pop(')')
            return ()
        value = self.parse()
        if self.tokens[self.i] == ',':
            self.pop(',')
            value = (value, self.parse())
        self.pop(')')
        return value

    def all(self):
        value = self.parse()
        need(self.i == len(self.tokens), 'Trailing tokens')
        return value


def label(vertex, n):
    if n == 0:
        need(vertex == (), 'Invalid singleton vertex')
        return 0
    if vertex is None:
        return n
    need(isinstance(vertex, tuple) and len(vertex) == 2 and vertex[0] == 'some', 'Invalid option vertex')
    return label(vertex[1], n-1)


def parents(tree, n):
    if n == 0:
        need(tree == (), 'Invalid singleton tree')
        return ()
    return parents(tree[0], n-1) + (label(tree[1], n-1),)


def adjacency(parent_list):
    graph = [set() for _ in range(len(parent_list)+1)]
    for vertex, parent in enumerate(parent_list, 1):
        need(0 <= parent < vertex, 'Invalid leaf-insertion parent')
        graph[vertex].add(parent)
        graph[parent].add(vertex)
    return graph


def shape_data(graph):
    @lru_cache(None)
    def shape(vertex, parent):
        return tuple(sorted(shape(w, vertex) for w in graph[vertex] if w != parent))
    return shape


def witness(source, target):
    source_shape, target_shape = shape_data(source), shape_data(target)
    need(source_shape(0, -1) == target_shape(0, -1), 'Different rooted shapes')
    mapping = [-1] * len(source)
    def match(a, pa, b, pb):
        mapping[a] = b
        left = sorted((source_shape(x, a), x) for x in source[a] if x != pa)
        right = sorted((target_shape(x, b), x) for x in target[b] if x != pb)
        need(len(left) == len(right), 'Different child counts')
        for (lc, x), (rc, y) in zip(left, right):
            need(lc == rc, 'Different child shape')
            match(x, a, y, b)
    match(0, -1, 0, -1)
    return mapping


def validate_map(source, target, mapping):
    size = len(source)
    need(len(target) == size and sorted(mapping) == list(range(size)) and mapping[0] == 0,
         'Not a root-preserving bijection')
    for a in range(size):
        for b in range(size):
            need((b in source[a]) == (mapping[b] in target[mapping[a]]), 'Adjacency is not preserved')


def reconstruct(source_bytes):
    need(hashlib.sha256(source_bytes).hexdigest() == SOURCE_SHA256, 'Changed original catalogue')
    text = source_bytes.decode()
    parsed = {int(n): FamilyParser(expr).all() for n, expr in
              re.findall(r'^def level(\d+) : List .*? := (\[.*\])$', text, re.M)}
    need(sorted(parsed) == list(range(11)), 'Wrong levels')
    need([len(parsed[n]) for n in range(11)] == EXPECTED_SIZES, 'Wrong catalogue sizes')
    catalogues = [[parents(tree, n) for tree in parsed[n]] for n in range(11)]
    graphs = [[adjacency(ps) for ps in row] for row in catalogues]
    indices = []
    for row in graphs:
        index = {}
        for j, graph in enumerate(row):
            key = shape_data(graph)(0, -1)
            need(key not in index, 'Duplicate rooted representative')
            index[key] = j
        indices.append(index)
    data = []
    for n in range(10):
        level = []
        for i, ps in enumerate(catalogues[n]):
            row = []
            for vertex in range(n+1):
                source = adjacency(ps + (vertex,))
                key = shape_data(source)(0, -1)
                need(key in indices[n+1], 'Uncovered transition ' + str((n, i, vertex)))
                j = indices[n+1][key]
                mapping = witness(source, graphs[n+1][j])
                validate_map(source, graphs[n+1][j], mapping)
                row.append({'target': j, 'map': mapping})
            level.append(row)
        data.append(level)
    count = 0
    for n, level in enumerate(data):
        for i, row in enumerate(level):
            for vertex, record in enumerate(row):
                validate_map(adjacency(catalogues[n][i] + (vertex,)),
                             graphs[n+1][record['target']], record['map'])
                count += 1
    need(count == 11210, 'Wrong transition count')
    for graph, bad_map in ((adjacency((0, 1)), [0, 2, 1]), (adjacency((0,)), [1, 0])):
        try:
            validate_map(graph, graph, bad_map)
        except ValueError:
            pass
        else:
            raise AssertionError('A deliberately wrong rooted map was accepted')
    raw = (json.dumps(data, separators=(',', ':')) + '\n').encode()
    need(hashlib.sha256(raw).hexdigest() == WITNESS_SHA256, 'Changed exact witness identities')
    report = {'status': 'EXACT_TRANSITION_WITNESSES_RECONSTRUCTED_NOT_KERNEL_PROOF',
              'catalogue_source_sha256': SOURCE_SHA256, 'witness_file_sha256': WITNESS_SHA256,
              'catalogue_sizes': EXPECTED_SIZES, 'rooted_catalogue_entries_checked': sum(EXPECTED_SIZES),
              'transitions': count, 'uncovered_transitions': 0, 'duplicate_rooted_representatives': 0,
              'transition_counts': [len(data[n])*(n+1) for n in range(10)],
              'every_full_vertex_bijection_and_ordered_adjacency_pair_checked': True,
              'wrong_same_size_map_rejected': True, 'wrong_root_rejected': True,
              'lean_transition_witness_check': 'NOT_YET_RUN', 'actual_tree_coverage_kernel_claim': False}
    return raw, report


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=root/'Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanRootedCatalogueData.lean')
    parser.add_argument('--output', type=Path, default=root/'Proofs/RG_Lean_20261019/build/catalogue_transition_candidates')
    args = parser.parse_args()
    raw, report = reconstruct(args.source.read_bytes())
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output/'catalogue_transition_witnesses.json').write_bytes(raw)
    (args.output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
