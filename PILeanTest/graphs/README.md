# Graph fixtures

The `.graph` files are dependency graphs of Lean projects and views of the neighbourhood of one
declaration in them (the declarations within a few edges of it), with every name removed: a
node keeps the length of its label, a cluster the length of its title, and nothing else is
stored. They are read by `GraphQuality.parseGraphFile` and measured by `GraphQuality.ioChecks`
(`lake test`) and by `lake exe pilean-test --graph-quality-files PILeanTest/graphs [DIR [packed]]`.

* `code-site-c.graph`: a code site of about 2,900 declarations in 85 modules, one cluster per
  module; `code-site-c-modules.graph`: its 85 modules and the dependencies between them;
  `code-site-c-largest-module.graph`: its largest module, in one cluster.
* `neighbourhood-N.graph`: views of the neighbourhood of one declaration with `N` nodes (the
  number is the count of nodes; `neighbourhood-star-401` is a node with 400 neighbours that
  have no other edges).

## Format

One item per line, fields separated by spaces; other lines are ignored.

* `n LENGTH SHAPE`: a node with a label of `LENGTH` letters; `e` for an ellipse, anything else
  (`b`) for a rounded box. Nodes are numbered from zero in the order of their lines.
* `e SRC DST`: an edge from node `SRC` to node `DST`.
* `c LENGTH PARENT MEMBERS...`: a cluster with a title of `LENGTH` letters, inside the cluster
  number `PARENT` (or `-1` for none), holding the nodes `MEMBERS`. Clusters are numbered from zero
  in the order of their lines.

## Recorded numbers

`dot-recorded.tsv` holds Graphviz's measures of the same graphs: the first line says which
version, then a header, then one row per graph with the number of nodes and edges, the number of
pairs of edges that cross, the total edge length in pixels and the area in square pixels. They
were made with `lake exe pilean-test --graph-quality DIR` (the built-in graphs) and
`lake exe pilean-test --graph-quality-files PILeanTest/graphs DIR` (these files), each followed by
`python3 -I tools/graph-compare.py DIR --tsv FILE`, which runs `dot -Tplain` on the Graphviz input
that the first step writes (PILean's node sizes and gaps, clusters as `cluster` subgraphs), flattens
its splines to polylines and counts as PILean's measures are counted. Rows named `NAME+packed`
were made with the `packed` mode of both tools (components laid out apart and packed: `pack=true`
for `dot`, `Graph.layoutPacked` for PILean).

`lake test` compares PILean's measures with these rows and needs no Graphviz; the rows are made
again only to refresh them.
