import Mathlib
import general.Common.Search

namespace Graph

/-! ### Build adjacency list and indegree array from edge list -/

/-- Build adjacency list and in-degree array from a list of directed edges.
Given `n` vertices (labeled `0..n-1`) and a list of edges `(u, v)`,
returns `(adj, indeg)` where:
- `adj[u]` is the list of out-neighbors of `u` (in reverse insertion order)
- `indeg[v]` is the in-degree (count of incoming edges) of `v`

Edges with endpoints ≥ `n` are silently ignored.
This is a standard preprocessing step for topological sort (Kahn's algorithm)
and other directed-graph DP problems. -/
def buildAdjacency (n : Nat) (edges : List (Nat × Nat)) : Array (List Nat) × Array Nat :=
  let initAdj := Array.mkArray n ([] : List Nat)
  let initIndeg := Array.mkArray n 0
  edges.foldl (λ (acc : Array (List Nat) × Array Nat) (u, v) =>
    if u < n && v < n then
      (acc.1.set! u (v :: acc.1[u]!), acc.2.set! v (acc.2[v]! + 1))
    else acc
  ) (initAdj, initIndeg)

/-- Build a weighted adjacency list from a list of directed edges `(src, dst, weight)`.
Given `n` vertices (labeled `0..n-1`), returns `adj` where `adj[u]` is the list of
`(v, w)` pairs for each outgoing edge `u → v` with weight `w`.
Edges with `src ≥ n` are silently ignored. -/
def buildWeightedAdjacency (n : Nat) (edges : List (Nat × Nat × Nat)) : Array (List (Nat × Nat)) :=
  edges.foldl (λ (acc : Array (List (Nat × Nat))) (u, v, w) =>
    if u < acc.size then
      let oldList := acc[u]!
      acc.set! u ((v, w) :: oldList)
    else acc
  ) (Array.mkArray n [])

/-! ### Undirected adjacency list -/

/-- Build an undirected adjacency list from a list of edges.
Given `n` vertices (labeled `0..n-1`) and a list of undirected edges `(u, v)`,
returns `adj` where `adj[i]` is the list of neighbors of `i` (in reverse insertion order).

Each edge `(u, v)` adds `v` to `adj[u]` and `u` to `adj[v]`.
Edges with endpoints ≥ `n` cause a panic (`.modify` with index out of bounds). -/
def buildUndirectedAdjacency (n : Nat) (edges : List (Nat × Nat)) : Array (List Nat) :=
  edges.foldl
    (fun adj e =>
      let adj₁ := adj.modify e.1 (fun lst => e.2 :: lst)
      let adj₂ := adj₁.modify e.2 (fun lst => e.1 :: lst)
      adj₂)
    (Array.mkArray n ([] : List Nat))

/-! ### Undirected weighted adjacency list -/

/-- Build an undirected weighted adjacency list from a list of edges `(u, v, weight)`.
    Given `n` vertices (labeled `0..n-1`), returns `adj` where `adj[u]` lists all
    `(neighbor, weight)` pairs incident to `u`.

    Each edge `(u, v, t)` adds `(v, t)` to `adj[u]` and `(u, t)` to `adj[v]`.
    Endpoints ≥ `n` cause a panic (`.set!` with index out of bounds). -/
def buildUndirectedWeightedAdjacency (n : Nat) (edges : List (Nat × Nat × Nat)) : Array (List (Nat × Nat)) :=
  edges.foldl (fun (acc : Array (List (Nat × Nat))) (edge : Nat × Nat × Nat) =>
    let (u, v, t) := edge
    let acc := acc.set! u ((v, t) :: acc[u]!)
    acc.set! v ((u, t) :: acc[v]!)
  ) (Array.mkArray n [])

/-! ### Simple undirected paths -/

/-- A predicate that checks whether `path` is a simple (no repeated nodes) path in the
undirected graph given by `edges`. Each consecutive pair in the path must be connected
by an edge in either direction.

Generic over the node type `α` ([`Inhabited α`] is required for the `path[i]!` accessor),
so it can be reused for any graph problem that needs to describe simple undirected paths. -/
def IsPath {α : Type} [Inhabited α] (path : List α) (edges : List (α × α)) : Prop :=
  path.Nodup ∧
  (∀ {i : Nat}, i < path.length - 1 →
    ((path[i]!, path[i + 1]!) ∈ edges ∨ (path[i + 1]!, path[i]!) ∈ edges))

/-! ### Reachability via step-indexed transitions -/

/-- Reachability via repeated applications of an operation.
    Parameterized by the operation for maximum reusability across transition systems.

    `Reachable op a b` means there exists a finite sequence of indices `i₁, …, iₖ`
    such that applying `op` at each index transforms `a` into `b`:
    `op a i₁ = some a₁`, `op a₁ i₂ = some a₂`, …, `op aₖ₋₁ iₖ = some b`.

    Useful for modeling step-indexed graph traversals, automata transitions,
    and any system where each step is labeled by a `Nat` index. -/
inductive Reachable {α : Type} (op : α → Nat → Option α) : α → α → Prop
  | refl (a) : Reachable op a a
  | step {a b c : α} (i : Nat) (h : op a i = some c) (hc : Reachable op c b) : Reachable op a b

/-! ### Edge validity predicates -/

/-- An edge `(a, b)` is in bounds for a graph on `n` vertices if both endpoints are `< n`. -/
def edgeInBounds (n : Nat) (e : Nat × Nat) : Prop :=
  e.1 < n ∧ e.2 < n

/-- An undirected edge is in canonical form: endpoints are in bounds and `a < b`.
    Many graph algorithms rely on this convention to avoid processing duplicate edges. -/
def canonicalEdge (n : Nat) (e : Nat × Nat) : Prop :=
  edgeInBounds n e ∧ e.1 < e.2

/-- A weighted edge `(a, b, w)` is valid in an `n`-node graph:
    both endpoints lie in `[0, n)`, they are distinct (no self-loops),
    and the weight is positive (`w ≥ 1`). -/
def validEdge (n : Nat) (e : Nat × Nat × Nat) : Prop :=
  let (a, b, w) := e
  a < n ∧ b < n ∧ a ≠ b ∧ w ≥ 1

/-- Every edge in the list satisfies `validEdge n`. -/
def allEdgesValid (n : Nat) (edges : List (Nat × Nat × Nat)) : Prop :=
  edges.Forall (validEdge n)

end Graph


namespace Search

/-! ### Fuel-bounded Breadth-First Search (BFS) -/

/-- Fuel-bounded breadth-first search for the shortest distance to a target state.

Given:
- `fuel`: maximum number of BFS layers to explore (guarantees termination)
- `next`: successor function from a state to its neighboring states
- `isTarget`: predicate identifying goal states
- `queue`: current BFS frontier (states to explore at the current depth)
- `visited`: all states seen so far (to avoid revisiting)
- `steps`: current distance from the start

Returns `some k` where `k` is the shortest distance to a target, or `none`
if the fuel is exhausted or the search space is exhausted without finding a target.

The caller typically invokes this as:
`bfsGo maxFuel next isTarget [start] [start] 0` -/
def bfsGo [BEq σ] (fuel : Nat) (next : σ → List σ) (isTarget : σ → Bool)
    (queue visited : List σ) (steps : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match queue with
    | [] => none
    | _ =>
      if queue.any isTarget then
        some steps
      else
        let candidates : List σ := queue.flatMap next
        let newStates : List σ := candidates.filter (fun s => !(visited.contains s))
        if newStates.isEmpty then none
        else bfsGo fuel' next isTarget newStates (visited ++ newStates) (steps + 1)

end Search

