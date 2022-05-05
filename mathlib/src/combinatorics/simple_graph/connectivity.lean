/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.list
/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `simple_graph.walk` (with accompanying pattern definitions
  `simple_graph.walk.nil'` and `simple_graph.walk.cons'`)

* `simple_graph.walk.is_trail`, `simple_graph.walk.is_path`, and `simple_graph.walk.is_cycle`.

* `simple_graph.path`

* `simple_graph.walk.map` and `simple_graph.path.map` for the induced map on walks,
  given an (injective) graph homomorphism.

* `simple_graph.reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `simple_graph.preconnected` and `simple_graph.connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `simple_graph.subgraph.connected` gives subgraphs the connectivity
  predicate via `simple_graph.subgraph.coe`.

* `simple_graph.connected_component` is the type of connected components of
  a given graph.

## Tags
walks, trails, paths, circuits, cycles

-/

universes u v

namespace simple_graph
variables {V : Type u} {V' : Type v} (G : simple_graph V) (G' : simple_graph V')

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `simple_graph.walk.support`.

See `simple_graph.walk.nil'` and `simple_graph.walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
@[derive decidable_eq]
inductive walk : V → V → Type u
| nil {u : V} : walk u u
| cons {u v w: V} (h : G.adj u v) (p : walk v w) : walk u w

attribute [refl] walk.nil

instance walk.inhabited (v : V) : inhabited (G.walk v v) := ⟨by refl⟩

namespace walk
variables {G}

/-- Pattern to get `walk.nil` with the vertex as an explicit argument. -/
@[pattern] abbreviation nil' (u : V) : G.walk u u := walk.nil

/-- Pattern to get `walk.cons` with the vertices as explicit arguments. -/
@[pattern] abbreviation cons' (u v w : V) (h : G.adj u v) (p : G.walk v w) : G.walk u w :=
walk.cons h p

lemma exists_eq_cons_of_ne : Π {u v : V} (hne : u ≠ v) (p : G.walk u v),
  ∃ (w : V) (h : G.adj u w) (p' : G.walk w v), p = cons h p'
| _ _ hne nil := (hne rfl).elim
| _ _ _ (cons h p') := ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
def length : Π {u v : V}, G.walk u v → ℕ
| _ _ nil := 0
| _ _ (cons _ q) := q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append : Π {u v w : V}, G.walk u v → G.walk v w → G.walk u w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := cons h (p.append q)

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverse_aux : Π {u v w : V}, G.walk u v → G.walk u w → G.walk v w
| _ _ _ nil q := q
| _ _ _ (cons h p) q := reverse_aux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.walk u v) : G.walk v u := w.reverse_aux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def get_vert : Π {u v : V} (p : G.walk u v) (n : ℕ), V
| u v nil _ := u
| u v (cons _ _) 0 := u
| u v (cons _ q) (n+1) := q.get_vert n

@[simp] lemma get_vert_zero {u v} (w : G.walk u v) : w.get_vert 0 = u :=
by { cases w; refl }

lemma get_vert_of_length_le {u v} (w : G.walk u v) {i : ℕ} (hi : w.length ≤ i) :
  w.get_vert i = v :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { refl },
  { cases i,
    { cases hi, },
    { exact IH (nat.succ_le_succ_iff.1 hi) } }
end

@[simp] lemma get_vert_length {u v} (w : G.walk u v) : w.get_vert w.length = v :=
w.get_vert_of_length_le rfl.le

lemma adj_get_vert_succ {u v} (w : G.walk u v) {i : ℕ} (hi : i < w.length) :
  G.adj (w.get_vert i) (w.get_vert (i+1)) :=
begin
  induction w with _ x y z hxy wyz IH generalizing i,
  { cases hi, },
  { cases i,
    { simp [get_vert, hxy] },
    { exact IH (nat.succ_lt_succ_iff.1 hi) } },
end

@[simp] lemma cons_append {u v w x : V} (h : G.adj u v) (p : G.walk v w) (q : G.walk w x) :
  (cons h p).append q = cons h (p.append q) := rfl

@[simp] lemma cons_nil_append {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h nil).append p = cons h p := rfl

@[simp] lemma append_nil : Π {u v : V} (p : G.walk u v), p.append nil = p
| _ _ nil := rfl
| _ _ (cons h p) := by rw [cons_append, append_nil]

@[simp] lemma nil_append {u v : V} (p : G.walk u v) : nil.append p = p := rfl

lemma append_assoc : Π {u v w x : V} (p : G.walk u v) (q : G.walk v w) (r : G.walk w x),
  p.append (q.append r) = (p.append q).append r
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by { dunfold append, rw append_assoc, }

@[simp] lemma reverse_nil {u : V} : (nil : G.walk u u).reverse = nil := rfl

lemma reverse_singleton {u v : V} (h : G.adj u v) :
  (cons h nil).reverse = cons (G.symm h) nil := rfl

@[simp] lemma cons_reverse_aux {u v w x : V} (p : G.walk u v) (q : G.walk w x) (h : G.adj w u) :
  (cons h p).reverse_aux q = p.reverse_aux (cons (G.symm h) q) := rfl

@[simp] protected lemma append_reverse_aux : Π {u v w x : V}
  (p : G.walk u v) (q : G.walk v w) (r : G.walk u x),
  (p.append q).reverse_aux r = q.reverse_aux (p.reverse_aux r)
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := append_reverse_aux p' q (cons (G.symm h) r)

@[simp] protected lemma reverse_aux_append : Π {u v w x : V}
  (p : G.walk u v) (q : G.walk u w) (r : G.walk w x),
  (p.reverse_aux q).append r = p.reverse_aux (q.append r)
| _ _ _ _ nil _ _ := rfl
| _ _ _ _ (cons h p') q r := by simp [reverse_aux_append p' (cons (G.symm h) q) r]

protected lemma reverse_aux_eq_reverse_append {u v w : V} (p : G.walk u v) (q : G.walk u w) :
  p.reverse_aux q = p.reverse.append q :=
by simp [reverse]

@[simp] lemma reverse_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) :=
by simp [reverse]

@[simp] lemma reverse_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).reverse = q.reverse.append p.reverse :=
by simp [reverse]

@[simp] lemma reverse_reverse : Π {u v : V} (p : G.walk u v), p.reverse.reverse = p
| _ _ nil := rfl
| _ _ (cons h p) := by simp [reverse_reverse]

@[simp] lemma length_nil {u : V} : (nil : G.walk u u).length = 0 := rfl

@[simp] lemma length_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).length = p.length + 1 := rfl

@[simp] lemma length_append : Π {u v w : V} (p : G.walk u v) (q : G.walk v w),
  (p.append q).length = p.length + q.length
| _ _ _ nil _ := by simp
| _ _ _ (cons _ _) _ := by simp [length_append, add_left_comm, add_comm]

@[simp] protected lemma length_reverse_aux : Π {u v w : V} (p : G.walk u v) (q : G.walk u w),
  (p.reverse_aux q).length = p.length + q.length
| _ _ _ nil _ := by simp!
| _ _ _ (cons _ _) _ := by simp [length_reverse_aux, nat.add_succ, nat.succ_add]

@[simp] lemma length_reverse {u v : V} (p : G.walk u v) : p.reverse.length = p.length :=
by simp [reverse]

lemma eq_of_length_eq_zero : Π {u v : V} {p : G.walk u v}, p.length = 0 → u = v
| _ _ nil _ := rfl

@[simp] lemma exists_length_eq_zero_iff {u v : V} : (∃ (p : G.walk u v), p.length = 0) ↔ u = v :=
begin
  split,
  { rintro ⟨p, hp⟩,
    exact eq_of_length_eq_zero hp, },
  { rintro rfl,
    exact ⟨nil, rfl⟩, },
end

@[simp] lemma length_eq_zero_iff {u : V} {p : G.walk u u} : p.length = 0 ↔ p = nil :=
by cases p; simp

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support : Π {u v : V}, G.walk u v → list V
| u v nil := [u]
| u v (cons h p) := u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts : Π {u v : V}, G.walk u v → list G.dart
| u v nil := []
| u v (cons h p) := ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `simple_graph.walk.darts`. -/
def edges {u v : V} (p : G.walk u v) : list (sym2 V) := p.darts.map dart.edge

@[simp] lemma support_nil {u : V} : (nil : G.walk u u).support = [u] := rfl

@[simp] lemma support_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).support = u :: p.support := rfl

lemma support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').support = p.support ++ p'.support.tail :=
by induction p; cases p'; simp [*]

@[simp]
lemma support_reverse {u v : V} (p : G.walk u v) : p.reverse.support = p.support.reverse :=
by induction p; simp [support_append, *]

lemma support_ne_nil {u v : V} (p : G.walk u v) : p.support ≠ [] :=
by cases p; simp

lemma tail_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').support.tail = p.support.tail ++ p'.support.tail :=
by rw [support_append, list.tail_append_of_ne_nil _ _ (support_ne_nil _)]

lemma support_eq_cons {u v : V} (p : G.walk u v) : p.support = u :: p.support.tail :=
by cases p; simp

@[simp] lemma start_mem_support {u v : V} (p : G.walk u v) : u ∈ p.support :=
by cases p; simp

@[simp] lemma end_mem_support {u v : V} (p : G.walk u v) : v ∈ p.support :=
by induction p; simp [*]

lemma mem_support_iff {u v w : V} (p : G.walk u v) :
  w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
by cases p; simp

lemma mem_support_nil_iff {u v : V} : u ∈ (nil : G.walk v v).support ↔ u = v := by simp

@[simp]
lemma mem_tail_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail :=
by rw [tail_support_append, list.mem_append]

@[simp] lemma end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.walk u v) :
  v ∈ p.support.tail :=
by { obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p, simp }

@[simp]
lemma mem_support_append_iff {t u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support :=
begin
  simp only [mem_support_iff, mem_tail_support_append_iff],
  by_cases h : t = v; by_cases h' : t = u;
  subst_vars;
  try { have := ne.symm h' };
  simp [*],
end

lemma coe_support {u v : V} (p : G.walk u v) :
  (p.support : multiset V) = {u} + p.support.tail :=
by cases p; refl

lemma coe_support_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  ((p.append p').support : multiset V) = {u} + p.support.tail + p'.support.tail :=
by rw [support_append, ←multiset.coe_add, coe_support]

lemma coe_support_append' [decidable_eq V] {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  ((p.append p').support : multiset V) = p.support + p'.support - {v} :=
begin
  rw [support_append, ←multiset.coe_add],
  simp only [coe_support],
  rw add_comm {v},
  simp only [← add_assoc, add_tsub_cancel_right],
end

lemma chain_adj_support : Π {u v w : V} (h : G.adj u v) (p : G.walk v w),
  list.chain G.adj u p.support
| _ _ _ h nil := list.chain.cons h list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_adj_support h' p)

lemma chain'_adj_support : Π {u v : V} (p : G.walk u v), list.chain' G.adj p.support
| _ _ nil := list.chain.nil
| _ _ (cons h p) := chain_adj_support h p

lemma chain_dart_adj_darts : Π {d : G.dart} {v w : V} (h : d.snd = v) (p : G.walk v w),
  list.chain G.dart_adj d p.darts
| _ _ _ h nil := list.chain.nil
| _ _ _ h (cons h' p) := list.chain.cons h (chain_dart_adj_darts (by exact rfl) p)

lemma chain'_dart_adj_darts : Π {u v : V} (p : G.walk u v), list.chain' G.dart_adj p.darts
| _ _ nil := trivial
| _ _ (cons h p) := chain_dart_adj_darts rfl p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
lemma edges_subset_edge_set : Π {u v : V} (p : G.walk u v) ⦃e : sym2 V⦄
  (h : e ∈ p.edges), e ∈ G.edge_set
| _ _ (cons h' p') e h := by rcases h with ⟨rfl, h⟩; solve_by_elim

@[simp] lemma darts_nil {u : V} : (nil : G.walk u u).darts = [] := rfl

@[simp] lemma darts_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

@[simp] lemma darts_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').darts = p.darts ++ p'.darts :=
by induction p; simp [*]

@[simp] lemma darts_reverse {u v : V} (p : G.walk u v) :
  p.reverse.darts = (p.darts.map dart.symm).reverse :=
by induction p; simp [*, sym2.eq_swap]

lemma cons_map_snd_darts {u v : V} (p : G.walk u v) :
  u :: p.darts.map dart.snd = p.support :=
by induction p; simp! [*]

lemma map_snd_darts {u v : V} (p : G.walk u v) :
  p.darts.map dart.snd = p.support.tail :=
by simpa using congr_arg list.tail (cons_map_snd_darts p)

lemma map_fst_darts_append {u v : V} (p : G.walk u v) :
  p.darts.map dart.fst ++ [v] = p.support :=
by induction p; simp! [*]

lemma map_fst_darts {u v : V} (p : G.walk u v) :
  p.darts.map dart.fst = p.support.init :=
by simpa! using congr_arg list.init (map_fst_darts_append p)

@[simp] lemma edges_nil {u : V} : (nil : G.walk u u).edges = [] := rfl

@[simp] lemma edges_cons {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).edges = ⟦(u, v)⟧ :: p.edges := rfl

@[simp] lemma edges_append {u v w : V} (p : G.walk u v) (p' : G.walk v w) :
  (p.append p').edges = p.edges ++ p'.edges :=
by simp [edges]

@[simp] lemma edges_reverse {u v : V} (p : G.walk u v) : p.reverse.edges = p.edges.reverse :=
by simp [edges]

@[simp] lemma length_support {u v : V} (p : G.walk u v) : p.support.length = p.length + 1 :=
by induction p; simp *

@[simp] lemma length_darts {u v : V} (p : G.walk u v) : p.darts.length = p.length :=
by induction p; simp *

@[simp] lemma length_edges {u v : V} (p : G.walk u v) : p.edges.length = p.length :=
by simp [edges]

lemma dart_fst_mem_support_of_mem_darts :
  Π {u v : V} (p : G.walk u v) {d : G.dart}, d ∈ p.darts → d.fst ∈ p.support
| u v (cons h p') d hd := begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { exact or.inl rfl, },
  { exact or.inr (dart_fst_mem_support_of_mem_darts _ hd), },
end

lemma dart_snd_mem_support_of_mem_darts :
  Π {u v : V} (p : G.walk u v) {d : G.dart}, d ∈ p.darts → d.snd ∈ p.support
| u v (cons h p') d hd := begin
  simp only [support_cons, darts_cons, list.mem_cons_iff] at hd ⊢,
  rcases hd with (rfl|hd),
  { simp },
  { exact or.inr (dart_snd_mem_support_of_mem_darts _ hd), },
end

lemma mem_support_of_mem_edges {t u v w : V} (p : G.walk v w) (he : ⟦(t, u)⟧ ∈ p.edges) :
  t ∈ p.support :=
begin
  obtain ⟨d, hd, he⟩ := list.mem_map.mp he,
  rw dart_edge_eq_mk_iff' at he,
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { exact dart_fst_mem_support_of_mem_darts _ hd, },
  { exact dart_snd_mem_support_of_mem_darts _ hd, },
end

lemma darts_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) :
  p.darts.nodup :=
begin
  induction p,
  { simp, },
  { simp only [darts_cons, support_cons, list.nodup_cons] at h ⊢,
    refine ⟨λ h', h.1 (dart_fst_mem_support_of_mem_darts p_p h'), p_ih h.2⟩, }
end

lemma edges_nodup_of_support_nodup {u v : V} {p : G.walk u v} (h : p.support.nodup) :
  p.edges.nodup :=
begin
  induction p,
  { simp, },
  { simp only [edges_cons, support_cons, list.nodup_cons] at h ⊢,
    exact ⟨λ h', h.1 (mem_support_of_mem_edges p_p h'), p_ih h.2⟩, }
end

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
structure is_trail {u v : V} (p : G.walk u v) : Prop :=
(edges_nodup : p.edges.nodup)

/-- A *path* is a walk with no repeating vertices.
Use `simple_graph.walk.is_path.mk'` for a simpler constructor. -/
structure is_path {u v : V} (p : G.walk u v) extends to_trail : is_trail p : Prop :=
(support_nodup : p.support.nodup)

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
structure is_circuit {u : V} (p : G.walk u u) extends to_trail : is_trail p : Prop :=
(ne_nil : p ≠ nil)

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure is_cycle {u : V} (p : G.walk u u)
  extends to_circuit : is_circuit p : Prop :=
(support_nodup : p.support.tail.nodup)

lemma is_trail_def {u v : V} (p : G.walk u v) : p.is_trail ↔ p.edges.nodup :=
⟨is_trail.edges_nodup, λ h, ⟨h⟩⟩

lemma is_path.mk' {u v : V} {p : G.walk u v} (h : p.support.nodup) : is_path p :=
⟨⟨edges_nodup_of_support_nodup h⟩, h⟩

lemma is_path_def {u v : V} (p : G.walk u v) : p.is_path ↔ p.support.nodup :=
⟨is_path.support_nodup, is_path.mk'⟩

lemma is_cycle_def {u : V} (p : G.walk u u) :
  p.is_cycle ↔ is_trail p ∧ p ≠ nil ∧ p.support.tail.nodup :=
iff.intro (λ h, ⟨h.1.1, h.1.2, h.2⟩) (λ h, ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

@[simp] lemma is_trail.nil {u : V} : (nil : G.walk u u).is_trail :=
⟨by simp [edges]⟩

lemma is_trail.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} :
  (cons h p).is_trail → p.is_trail :=
by simp [is_trail_def]

@[simp] lemma cons_is_trail_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_trail ↔ p.is_trail ∧ ⟦(u, v)⟧ ∉ p.edges :=
by simp [is_trail_def, and_comm]

lemma is_trail.reverse {u v : V} (p : G.walk u v) (h : p.is_trail) : p.reverse.is_trail :=
by simpa [is_trail_def] using h

@[simp] lemma reverse_is_trail_iff {u v : V} (p : G.walk u v) : p.reverse.is_trail ↔ p.is_trail :=
by split; { intro h, convert h.reverse _, try { rw reverse_reverse } }

lemma is_trail.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_trail) : p.is_trail :=
by { rw [is_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.1⟩ }

lemma is_trail.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_trail) : q.is_trail :=
by { rw [is_trail_def, edges_append, list.nodup_append] at h, exact ⟨h.2.1⟩ }

lemma is_trail.count_edges_le_one [decidable_eq V] {u v : V}
  {p : G.walk u v} (h : p.is_trail) (e : sym2 V) : p.edges.count e ≤ 1 :=
list.nodup_iff_count_le_one.mp h.edges_nodup e

lemma is_trail.count_edges_eq_one [decidable_eq V] {u v : V}
  {p : G.walk u v} (h : p.is_trail) {e : sym2 V} (he : e ∈ p.edges) :
  p.edges.count e = 1 :=
list.count_eq_one_of_mem h.edges_nodup he

@[simp] lemma is_path.nil {u : V} : (nil : G.walk u u).is_path :=
by { fsplit; simp }

lemma is_path.of_cons {u v w : V} {h : G.adj u v} {p : G.walk v w} :
  (cons h p).is_path → p.is_path :=
by simp [is_path_def]

@[simp] lemma cons_is_path_iff {u v w : V} (h : G.adj u v) (p : G.walk v w) :
  (cons h p).is_path ↔ p.is_path ∧ u ∉ p.support :=
by split; simp [is_path_def] { contextual := tt }

lemma is_path.reverse {u v : V} {p : G.walk u v} (h : p.is_path) : p.reverse.is_path :=
by simpa [is_path_def] using h

@[simp] lemma is_path_reverse_iff {u v : V} (p : G.walk u v) : p.reverse.is_path ↔ p.is_path :=
by split; intro h; convert h.reverse; simp

lemma is_path.of_append_left {u v w : V} {p : G.walk u v} {q : G.walk v w} :
  (p.append q).is_path → p.is_path :=
by { simp only [is_path_def, support_append], exact list.nodup.of_append_left }

lemma is_path.of_append_right {u v w : V} {p : G.walk u v} {q : G.walk v w}
  (h : (p.append q).is_path) : q.is_path :=
begin
  rw ←is_path_reverse_iff at h ⊢,
  rw reverse_append at h,
  apply h.of_append_left,
end

/-! ### Walk decompositions -/

section walk_decomp
variables [decidable_eq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def take_until : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk v u
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by subst u
  else cons r (take_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id)

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def drop_until : Π {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support), G.walk u w
| v w nil u h := by rw mem_support_nil_iff.mp h
| v w (cons r p) u h :=
  if hx : v = u
  then by { subst u, exact cons r p }
  else drop_until p _ $ h.cases_on (λ h', (hx h'.symm).elim) id

/-- The `take_until` and `drop_until` functions split a walk into two pieces.
The lemma `count_support_take_until_eq_one` specifies where this split occurs. -/
@[simp]
lemma take_spec {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).append (p.drop_until u h) = p :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    refl, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; subst_vars; simp [*], } },
end

@[simp]
lemma count_support_take_until_eq_one {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support.count u = 1 :=
begin
  induction p,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp! },
    { simp! only,
      split_ifs with h'; rw eq_comm at h'; subst_vars; simp! [*, list.count_cons], } },
end

lemma count_edges_take_until_le_one {u v w : V} (p : G.walk v w) (h : u ∈ p.support) (x : V) :
  (p.take_until u h).edges.count ⟦(u, x)⟧ ≤ 1 :=
begin
  induction p with u' u' v' w' ha p' ih,
  { rw mem_support_nil_iff at h,
    subst u,
    simp!, },
  { obtain (rfl|h) := h,
    { simp!, },
    { simp! only,
      split_ifs with h',
      { subst h',
        simp, },
      { rw [edges_cons, list.count_cons],
        split_ifs with h'',
        { rw sym2.eq_iff at h'',
          obtain (⟨rfl,rfl⟩|⟨rfl,rfl⟩) := h'',
          { exact (h' rfl).elim },
          { cases p'; simp! } },
        { apply ih, } } } },
end

lemma support_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inl hx }

lemma support_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).support ⊆ p.support :=
λ x hx, by { rw [← take_spec p h, mem_support_append_iff], exact or.inr hx }

lemma darts_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inl hx }

lemma darts_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).darts ⊆ p.darts :=
λ x hx, by { rw [← take_spec p h, darts_append, list.mem_append], exact or.inr hx }

lemma edges_take_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_take_until_subset h)

lemma edges_drop_until_subset {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).edges ⊆ p.edges :=
list.map_subset _ (p.darts_drop_until_subset h)

lemma length_take_until_le {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.take_until u h).length ≤ p.length :=
begin
  have := congr_arg walk.length (p.take_spec h),
  rw [length_append] at this,
  exact nat.le.intro this,
end

lemma length_drop_until_le {u v w : V} (p : G.walk v w) (h : u ∈ p.support) :
  (p.drop_until u h).length ≤ p.length :=
begin
  have := congr_arg walk.length (p.take_spec h),
  rw [length_append, add_comm] at this,
  exact nat.le.intro this,
end

protected
lemma is_trail.take_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.take_until u h).is_trail :=
is_trail.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_trail.drop_until {u v w : V} {p : G.walk v w} (hc : p.is_trail) (h : u ∈ p.support) :
  (p.drop_until u h).is_trail :=
is_trail.of_append_right (by rwa ← take_spec _ h at hc)

protected
lemma is_path.take_until {u v w : V} {p : G.walk v w} (hc : p.is_path) (h : u ∈ p.support) :
  (p.take_until u h).is_path :=
is_path.of_append_left (by rwa ← take_spec _ h at hc)

protected
lemma is_path.drop_until {u v w : V} (p : G.walk v w) (hc : p.is_path) (h : u ∈ p.support) :
  (p.drop_until u h).is_path :=
is_path.of_append_right (by rwa ← take_spec _ h at hc)

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) : G.walk u u :=
(c.drop_until u h).append (c.take_until u h)

@[simp]
lemma support_rotate {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).support.tail ~r c.support.tail :=
begin
  simp only [rotate, tail_support_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←tail_support_append, take_spec],
end

lemma rotate_darts {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).darts ~r c.darts :=
begin
  simp only [rotate, darts_append],
  apply list.is_rotated.trans list.is_rotated_append,
  rw [←darts_append, take_spec],
end

lemma rotate_edges {u v : V} (c : G.walk v v) (h : u ∈ c.support) :
  (c.rotate h).edges ~r c.edges :=
(rotate_darts c h).map _

protected
lemma is_trail.rotate {u v : V} {c : G.walk v v} (hc : c.is_trail) (h : u ∈ c.support) :
  (c.rotate h).is_trail :=
begin
  rw [is_trail_def, (c.rotate_edges h).perm.nodup_iff],
  exact hc.edges_nodup,
end

protected
lemma is_circuit.rotate {u v : V} {c : G.walk v v} (hc : c.is_circuit) (h : u ∈ c.support) :
  (c.rotate h).is_circuit :=
begin
  refine ⟨hc.to_trail.rotate _, _⟩,
  cases c,
  { exact (hc.ne_nil rfl).elim, },
  { intro hn,
    have hn' := congr_arg length hn,
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn',
    simpa using hn', },
end

protected
lemma is_cycle.rotate {u v : V} {c : G.walk v v} (hc : c.is_cycle) (h : u ∈ c.support) :
  (c.rotate h).is_cycle :=
begin
  refine ⟨hc.to_circuit.rotate _, _⟩,
  rw list.is_rotated.nodup_iff (support_rotate _ _),
  exact hc.support_nodup,
end

end walk_decomp

end walk

/-! ### Walks to paths -/

/-- The type for paths between two vertices. -/
abbreviation path (u v : V) := {p : G.walk u v // p.is_path}

namespace walk
variables {G} [decidable_eq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `simple_graph.walk.bypass_is_path`.
This is packaged up in `simple_graph.walk.to_path`. -/
def bypass : Π {u v : V}, G.walk u v → G.walk u v
| u v nil := nil
| u v (cons ha p) :=
  let p' := p.bypass
  in if hs : u ∈ p'.support
     then p'.drop_until u hs
     else cons ha p'

lemma bypass_is_path {u v : V} (p : G.walk u v) : p.bypass.is_path :=
begin
  induction p,
  { simp!, },
  { simp only [bypass],
    split_ifs,
    { apply is_path.drop_until,
      assumption, },
    { simp [*, cons_is_path_iff], } },
end

lemma length_bypass_le {u v : V} (p : G.walk u v) : p.bypass.length ≤ p.length :=
begin
  induction p,
  { refl },
  { simp only [bypass],
    split_ifs,
    { transitivity,
      apply length_drop_until_le,
      rw [length_cons],
      exact le_add_right p_ih, },
    { rw [length_cons, length_cons],
      exact add_le_add_right p_ih 1, } },
end

/-- Given a walk, produces a path with the same endpoints using `simple_graph.walk.bypass`. -/
def to_path {u v : V} (p : G.walk u v) : G.path u v := ⟨p.bypass, p.bypass_is_path⟩

lemma support_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.support ⊆ p.support :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (support_drop_until_subset _ _),
      apply list.subset_cons_of_subset,
      assumption, },
    { rw support_cons,
      apply list.cons_subset_cons,
      assumption, }, },
end

lemma support_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).support ⊆ p.support :=
support_bypass_subset _

lemma darts_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.darts ⊆ p.darts :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    { apply list.subset.trans (darts_drop_until_subset _ _),
      apply list.subset_cons_of_subset _ p_ih, },
    { rw darts_cons,
      exact list.cons_subset_cons _ p_ih, }, },
end

lemma edges_bypass_subset {u v : V} (p : G.walk u v) : p.bypass.edges ⊆ p.edges :=
list.map_subset _ p.darts_bypass_subset

lemma darts_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).darts ⊆ p.darts :=
darts_bypass_subset _

lemma edges_to_path_subset {u v : V} (p : G.walk u v) :
  (p.to_path : G.walk u v).edges ⊆ p.edges :=
edges_bypass_subset _

end walk

/-! ## Mapping paths -/

namespace walk
variables {G G'}

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') : Π {u v : V}, G.walk u v → G'.walk (f u) (f v)
| _ _ nil := nil
| _ _ (cons h p) := cons (f.map_adj h) (map p)

variables (f : G →g G') {u v : V} (p : G.walk u v)

@[simp] lemma map_nil : (nil : G.walk u u).map f = nil := rfl

@[simp] lemma map_cons {w : V} (h : G.adj w u) :
  (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl

@[simp] lemma length_map : (p.map f).length = p.length :=
by induction p; simp [*]

lemma map_append {u v w : V} (p : G.walk u v) (q : G.walk v w) :
  (p.append q).map f = (p.map f).append (q.map f) :=
by induction p; simp [*]

@[simp] lemma reverse_map : (p.map f).reverse = p.reverse.map f :=
by induction p; simp [map_append, *]

@[simp] lemma support_map : (p.map f).support = p.support.map f :=
by induction p; simp [*]

@[simp] lemma darts_map : (p.map f).darts = p.darts.map f.map_dart :=
by induction p; simp [*]

@[simp] lemma edges_map : (p.map f).edges = p.edges.map (sym2.map f) :=
by induction p; simp [*]

lemma map_is_path_of_injective (hinj : function.injective f) (hp : p.is_path) :
  (p.map f).is_path :=
begin
  induction p with w u v w huv hvw ih,
  { simp, },
  { rw walk.cons_is_path_iff at hp,
    simp [ih hp.1],
    intros x hx hf,
    cases hinj hf,
    exact hp.2 hx, },
end

lemma map_injective_of_injective {f : G →g G'} (hinj : function.injective f) (u v : V) :
  function.injective (walk.map f : G.walk u v → G'.walk (f u) (f v)) :=
begin
  intros p p' h,
  induction p with _ _ _ _ _ _ ih generalizing p',
  { cases p',
    { refl },
    simpa using h, },
  { induction p',
    { simpa using h, },
    { simp only [map_cons] at h,
      cases hinj h.1,
      simp only [eq_self_iff_true, heq_iff_eq, true_and],
      apply ih,
      simpa using h.2, } },
end

end walk

namespace path
variables {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps] protected def map (f : G →g G') (hinj : function.injective f) {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
⟨walk.map f p, walk.map_is_path_of_injective f p hinj p.2⟩

lemma map_injective {f : G →g G'} (hinj : function.injective f) (u v : V) :
  function.injective (path.map f hinj : G.path u v → G'.path (f u) (f v)) :=
begin
  rintros ⟨p, hp⟩ ⟨p', hp'⟩ h,
  simp only [path.map, subtype.coe_mk] at h,
  simp [walk.map_injective_of_injective hinj u v h],
end

/-- Given a graph embedding, map paths to paths. -/
@[simps] protected def map_embedding (f : G ↪g G') {u v : V} (p : G.path u v) :
  G'.path (f u) (f v) :=
path.map f.to_hom f.injective p

lemma map_embedding_injective (f : G ↪g G') (u v : V) :
  function.injective (path.map_embedding f : G.path u v → G'.path (f u) (f v)) :=
map_injective f.injective u v

end path

/-! ## `reachable` and `connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `relation.refl_trans_gen` of `G.adj`.
See `simple_graph.reachable_iff_refl_trans_gen`. -/
def reachable (u v : V) : Prop := nonempty (G.walk u v)

variables {G}

lemma reachable_iff_nonempty_univ {u v : V} :
  G.reachable u v ↔ (set.univ : set (G.walk u v)).nonempty :=
set.nonempty_iff_univ_nonempty

protected lemma reachable.elim {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.walk u v → p) : p :=
nonempty.elim h hp

protected lemma reachable.elim_path {p : Prop} {u v : V}
  (h : G.reachable u v) (hp : G.path u v → p) : p :=
begin
  classical,
  exact h.elim (λ q, hp q.to_path),
end

@[refl] protected lemma reachable.refl {u : V} : G.reachable u u := by { fsplit, refl }

@[symm] protected lemma reachable.symm {u v : V} (huv : G.reachable u v) : G.reachable v u :=
huv.elim (λ p, ⟨p.reverse⟩)

@[trans] protected lemma reachable.trans {u v w : V}
  (huv : G.reachable u v) (hvw : G.reachable v w) :
  G.reachable u w :=
huv.elim (λ puv, hvw.elim (λ pvw, ⟨puv.append pvw⟩))

lemma reachable_iff_refl_trans_gen (u v : V) :
  G.reachable u v ↔ relation.refl_trans_gen G.adj u v :=
begin
  split,
  { rintro ⟨h⟩,
    induction h,
    { refl, },
    { exact (relation.refl_trans_gen.single h_h).trans h_ih, }, },
  { intro h,
    induction h with _ _ _ ha hr,
    { refl, },
    { exact reachable.trans hr ⟨walk.cons ha walk.nil⟩, }, },
end

variables (G)

lemma reachable_is_equivalence : equivalence G.reachable :=
mk_equivalence _ (@reachable.refl _ G) (@reachable.symm _ G) (@reachable.trans _ G)

/-- The equivalence relation on vertices given by `simple_graph.reachable`. -/
def reachable_setoid : setoid V := setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def preconnected : Prop := ∀ (u v : V), G.reachable u v

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `has_coe_to_fun` instance so that `h u v` can be used instead
of `h.preconnected u v`. -/
@[protect_proj]
structure connected : Prop :=
(preconnected : G.preconnected)
(nonempty : nonempty V)

instance : has_coe_to_fun G.connected (λ _, Π (u v : V), G.reachable u v) :=
⟨λ h, h.preconnected⟩

/-- The quotient of `V` by the `simple_graph.reachable` relation gives the connected
components of a graph. -/
def connected_component := quot G.reachable

/-- Gives the connected component containing a particular vertex. -/
def connected_component_mk (v : V) : G.connected_component := quot.mk G.reachable v

instance connected_component.inhabited [inhabited V] : inhabited G.connected_component :=
⟨G.connected_component_mk default⟩

section connected_component
variables {G}

@[elab_as_eliminator]
protected lemma connected_component.ind {β : G.connected_component → Prop}
  (h : ∀ (v : V), β (G.connected_component_mk v)) (c : G.connected_component) : β c :=
quot.ind h c

@[elab_as_eliminator]
protected lemma connected_component.ind₂ {β : G.connected_component → G.connected_component → Prop}
  (h : ∀ (v w : V), β (G.connected_component_mk v) (G.connected_component_mk w))
  (c d : G.connected_component) : β c d :=
quot.induction_on₂ c d h

protected lemma connected_component.sound {v w : V} :
  G.reachable v w → G.connected_component_mk v = G.connected_component_mk w := quot.sound

protected lemma connected_component.exact {v w : V} :
  G.connected_component_mk v = G.connected_component_mk w → G.reachable v w :=
@quotient.exact _ G.reachable_setoid _ _

@[simp] protected lemma connected_component.eq {v w : V} :
  G.connected_component_mk v = G.connected_component_mk w ↔ G.reachable v w :=
@quotient.eq _ G.reachable_setoid _ _

/-- The `connected_component` specialization of `quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def connected_component.lift {β : Sort*} (f : V → β)
  (h : ∀ (v w : V) (p : G.walk v w), p.is_path → f v = f w) : G.connected_component → β :=
quot.lift f (λ v w (h' : G.reachable v w), h'.elim_path (λ hp, h v w hp hp.2))

@[simp] protected lemma connected_component.lift_mk {β : Sort*} {f : V → β}
  {h : ∀ (v w : V) (p : G.walk v w), p.is_path → f v = f w} {v : V} :
  connected_component.lift f h (G.connected_component_mk v) = f v := rfl

protected lemma connected_component.«exists» {p : G.connected_component → Prop} :
  (∃ (c : G.connected_component), p c) ↔ ∃ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).exists

protected lemma connected_component.«forall» {p : G.connected_component → Prop} :
  (∀ (c : G.connected_component), p c) ↔ ∀ v, p (G.connected_component_mk v) :=
(surjective_quot_mk G.reachable).forall

lemma preconnected.subsingleton_connected_component (h : G.preconnected) :
  subsingleton G.connected_component :=
⟨connected_component.ind₂ (λ v w, connected_component.sound (h v w))⟩

end connected_component

variables {G}

/-- A subgraph is connected if it is connected as a simple graph. -/
abbreviation subgraph.connected (H : G.subgraph) : Prop := H.coe.connected

lemma preconnected.set_univ_walk_nonempty (hconn : G.preconnected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty :=
by { rw ← set.nonempty_iff_univ_nonempty, exact hconn u v }

lemma connected.set_univ_walk_nonempty (hconn : G.connected) (u v : V) :
  (set.univ : set (G.walk u v)).nonempty := hconn.preconnected.set_univ_walk_nonempty u v

/-! ### Walks of a given length -/

section walk_counting

lemma set_walk_self_length_zero_eq (u : V) :
  {p : G.walk u u | p.length = 0} = {walk.nil} :=
by { ext p, simp }

lemma set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
  {p : G.walk u v | p.length = 0} = ∅ :=
begin
  ext p,
  simp only [set.mem_set_of_eq, set.mem_empty_eq, iff_false],
  exact λ h', absurd (walk.eq_of_length_eq_zero h') h,
end

lemma set_walk_length_succ_eq (u v : V) (n : ℕ) :
  {p : G.walk u v | p.length = n.succ} =
    ⋃ (w : V) (h : G.adj u w), walk.cons h '' {p' : G.walk w v | p'.length = n} :=
begin
  ext p,
  cases p with _ _ w _ huw pwv,
  { simp [eq_comm], },
  { simp only [nat.succ_eq_add_one, set.mem_set_of_eq, walk.length_cons, add_left_inj,
      set.mem_Union, set.mem_image, exists_prop],
    split,
    { rintro rfl,
      exact ⟨w, huw, pwv, rfl, rfl, heq.rfl⟩, },
    { rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩,
      refl, } },
end

variables (G) [fintype V] [decidable_rel G.adj] [decidable_eq V]

/-- The `finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `simple_graph.coe_finset_walk_length_eq` for the relationship between this `finset` and
the set of length-`n` walks. -/
def finset_walk_length : Π (n : ℕ) (u v : V), finset (G.walk u v)
| 0 u v := if h : u = v
           then by { subst u, exact {walk.nil} }
           else ∅
| (n+1) u v := finset.univ.bUnion (λ (w : V),
                 if h : G.adj u w
                 then (finset_walk_length n w v).map ⟨λ p, walk.cons h p, λ p q, by simp⟩
                 else ∅)

lemma coe_finset_walk_length_eq (n : ℕ) (u v : V) :
  (G.finset_walk_length n u v : set (G.walk u v)) = {p : G.walk u v | p.length = n} :=
begin
  induction n with n ih generalizing u v,
  { obtain rfl | huv := eq_or_ne u v;
    simp [finset_walk_length, set_walk_length_zero_eq_of_ne, *], },
  { simp only [finset_walk_length, set_walk_length_succ_eq,
      finset.coe_bUnion, finset.mem_coe, finset.mem_univ, set.Union_true],
    ext p,
    simp only [set.mem_Union, finset.mem_coe, set.mem_image, set.mem_set_of_eq],
    congr' 2,
    ext w,
    simp only [set.ext_iff, finset.mem_coe, set.mem_set_of_eq] at ih,
    split_ifs with huw; simp [huw, ih], },
end

variables {G}

lemma walk.length_eq_of_mem_finset_walk_length {n : ℕ} {u v : V} (p : G.walk u v) :
  p ∈ G.finset_walk_length n u v → p.length = n :=
(set.ext_iff.mp (G.coe_finset_walk_length_eq n u v) p).mp

variables (G)

instance fintype_set_walk_length (u v : V) (n : ℕ) : fintype {p : G.walk u v | p.length = n} :=
fintype.subtype (G.finset_walk_length n u v) $ λ p,
by rw [←finset.mem_coe, coe_finset_walk_length_eq]

lemma set_walk_length_to_finset_eq (n : ℕ) (u v : V) :
  {p : G.walk u v | p.length = n}.to_finset = G.finset_walk_length n u v :=
by { ext p, simp [←coe_finset_walk_length_eq] }

/- See `simple_graph.adj_matrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
lemma card_set_walk_length_eq (u v : V) (n : ℕ) :
  fintype.card {p : G.walk u v | p.length = n} = (G.finset_walk_length n u v).card :=
fintype.card_of_subtype (G.finset_walk_length n u v) $ λ p,
by rw [←finset.mem_coe, coe_finset_walk_length_eq]

end walk_counting

end simple_graph
