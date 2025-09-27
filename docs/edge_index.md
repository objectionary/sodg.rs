# Edge index design note

## Overview

Outbound edges on a vertex are exposed through `Sodg::kids`, which must remain
fast for both sparse and dense vertices. The `EdgeIndex` helps by providing an
adaptive mapping from interned label identifiers to destination vertex ids.

## Rationale

* **Small graph bias:** Most vertices in EO programs have a handful of outbound
  edges. A fixed-capacity `micromap::Map` keeps those lookups allocation-free and
  iteration-friendly.
* **Seamless growth:** Vertices that grow beyond 32 distinct labels transparently
  promote the index to a standard `HashMap`. This keeps lookup complexity at
  `O(1)` without imposing hash-table costs on the common, tiny case.
* **Label interning:** Storing `LabelId` instead of `Label` drastically reduces
  the size of the keys inside the index, improving cache locality for traversal
  heavy workloads.

## Trade-offs

* **Promotion cost:** The first insertion beyond the small-map threshold walks
  the entire map to populate the `HashMap`. Benchmarks show this one-time cost is
  more than offset by faster lookups in the dense regime.
* **Growth-aware promotion:** Promotion allocates the destination `HashMap`
  using a doubling growth factor and eagerly reserves for the next expansion to
  smoothen allocations across the 30–40 degree window. Callers should expect the
  amortized cost of inserts to stay nearly flat after the first promotion.
* **Two sources of truth:** The vertex keeps the `Vec<Edge>` as the canonical
  record while the index mirrors it. Tests assert that rebuilds and removals keep
  the two data structures synchronized.
* **Identifier limits:** `LabelId` and encoded vertex identifiers are `u32` to
  keep the index compact. Consumers must ensure the graph size stays within the
  representable range.

## Maintenance tips

* When changing the promotion threshold, update both `SMALL_THRESHOLD` and the
  benchmark scenarios in `benches/bench.rs` to keep performance coverage honest.
* Any new mutation on `Vertex` must update the index alongside the edge list;
  add regression tests whenever you introduce a new code path.
* The label interner guarantees that equal labels share an identifier. If the
  interner changes, revisit the debug assertions in the iterator implementation
  to keep the mirror intact.
