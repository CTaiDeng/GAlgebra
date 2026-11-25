import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

structure DirectedGraph (V E : Type _) where
  source : E → V
  target : E → V

namespace DirectedGraph

variable {V E : Type _}

inductive Path (G : DirectedGraph V E) : V → V → Type _
  | nil (v : V) : Path G v v
  | cons (e : E) {z : V} : Path G (G.target e) z → Path G (G.source e) z

def pathSum {G : DirectedGraph V E} {F : Type _} [Abelian F]
    (basis : E → F) {x y : V} : G.Path x y → F
  | .nil _ => 0
  | .cons e p => basis e + pathSum basis p

theorem path_boundary {G : DirectedGraph V E} {F A : Type _} [Abelian F] [Abelian A]
    (edge : E → F) (vertex : V → A) (D : AddMap F A)
    (edges : ∀ e, D (edge e) = vertex (G.target e) + -vertex (G.source e))
    {x y : V} (p : G.Path x y) :
    D (pathSum edge p) = vertex y + -vertex x := by
  induction p with
  | nil _ => simp [pathSum]
  | cons e _ ih =>
    rw [pathSum, D.map_add, edges, ih]
    exact Abelian.telescopes _ _ _

theorem face_boundary_zero {G : DirectedGraph V E} {F A : Type _} [Abelian F] [Abelian A]
    (edge : E → F) (vertex : V → A) (D : AddMap F A)
    (edges : ∀ e, D (edge e) = vertex (G.target e) + -vertex (G.source e))
    {x y : V} (p q : G.Path x y) :
    D (pathSum edge p + -pathSum edge q) = 0 := by
  rw [D.map_add, D.map_neg, path_boundary edge vertex D edges p,
    path_boundary edge vertex D edges q, Abelian.add_neg]

def append {G : DirectedGraph V E} {x y z : V} : G.Path x y → G.Path y z → G.Path x z
  | .nil _, v => v
  | .cons e u, v => .cons e (append u v)

theorem path_sum_append {G : DirectedGraph V E} {F : Type _} [Abelian F]
    (edge : E → F) {x y z : V} (p : G.Path x y) (q : G.Path y z) :
    pathSum edge (append p q) = pathSum edge p + pathSum edge q := by
  induction p with
  | nil _ => simp [append, pathSum]
  | cons e _ ih => simp [append, pathSum, ih, Abelian.assoc]

def pathEdges {G : DirectedGraph V E} {x y : V} : G.Path x y → List E
  | .nil _ => []
  | .cons e rest => e :: pathEdges rest

theorem path_potential_bound {G : DirectedGraph V E} (weight : E → Rat)
    (potential : V → Rat) (allowance : Rat)
    (edgeBound : ∀ e, weight e ≤ allowance + potential (G.target e) - potential (G.source e))
    {x y : V} (path : G.Path x y) :
    pathSum weight path ≤ (pathEdges path).length * allowance + potential y - potential x := by
  induction path with
  | nil _ => simp [pathSum, pathEdges, Rat.sub_self]
  | cons edge rest ih =>
    have edgeStep := edgeBound edge
    simp only [pathSum, pathEdges, List.length_cons, Rat.natCast_add, Rat.natCast_ofNat]
    grind

private def extendHit {n : Nat} (G : DirectedGraph (Fin n) E) (weight : E → Nat)
    (suffixes : Vector (Option (Nat × List E)) n) (edge : E) : Option (Nat × List E) :=
  (suffixes.get (G.target edge)).map (fun result => (weight edge + result.1, edge :: result.2))

private theorem get_ofFn_fin {A : Type _} {n : Nat} (f : Fin n → A) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

/-- A table at depth k stores a least-cost hit of length at most k at each vertex. -/
def hitTable {n : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v}) (weight : E → Nat)
    (goal : Fin n → Bool) : Nat → Vector (Option (Nat × List E)) n
  | 0 => Vector.ofFn (fun v => if goal v then some (0, []) else none)
  | k + 1 =>
    let suffixes := G.hitTable outgoing weight goal k
    Vector.ofFn (fun v =>
      if goal v then some (0, []) else
        ((outgoing v).filterMap (fun e => G.extendHit weight suffixes e.val)).minOn? Prod.fst)

theorem finite_hit_sound {n : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (weight : E → Nat) (goal : Fin n → Bool)
    (limit : Nat) (start : Fin n) (cost : Nat) (edges : List E)
    (found : (G.hitTable outgoing weight goal limit).get start = some (cost, edges)) :
    ∃ finish : Fin n, ∃ path : G.Path start finish,
      goal finish = true ∧ (pathEdges path).length ≤ limit ∧
      pathEdges path = edges ∧ ((pathEdges path).map weight).sum = cost := by
  induction limit generalizing start cost edges with
  | zero =>
    by_cases terminal : goal start = true
    · simp [hitTable, get_ofFn_fin, terminal] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨start, .nil start, terminal, by simp [pathEdges], rfl, rfl⟩
    · simp [hitTable, get_ofFn_fin, terminal] at found
  | succ limit ih =>
    by_cases terminal : goal start = true
    · simp [hitTable, get_ofFn_fin, terminal] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨start, .nil start, terminal, by simp [pathEdges], rfl, rfl⟩
    · simp only [hitTable, get_ofFn_fin, terminal] at found
      obtain ⟨edge, _, returned⟩ := List.mem_filterMap.mp (List.minOn?_mem found)
      cases suffix : (G.hitTable outgoing weight goal limit).get (G.target edge.val) with
      | none => simp [extendHit, suffix] at returned
      | some result =>
        obtain ⟨suffixCost, suffixEdges⟩ := result
        obtain ⟨finish, path, checked, length, recorded, charged⟩ :=
          ih (G.target edge.val) suffixCost suffixEdges suffix
        obtain ⟨edge, rfl⟩ := edge
        simp [extendHit, suffix] at returned
        obtain ⟨rfl, rfl⟩ := returned
        exact ⟨finish, .cons edge path, checked, by simp [pathEdges]; omega,
          by simp [pathEdges, recorded], by simp [pathEdges, charged]⟩

theorem finite_hit_complete_and_minimal {n : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (complete : ∀ e : E, ⟨e, rfl⟩ ∈ outgoing (G.source e))
    (weight : E → Nat) (goal : Fin n → Bool)
    (limit : Nat) {start finish : Fin n} (path : G.Path start finish)
    (terminal : goal finish = true) (within : (pathEdges path).length ≤ limit) :
    ∃ result, (G.hitTable outgoing weight goal limit).get start = some result ∧
      result.1 ≤ ((pathEdges path).map weight).sum := by
  induction limit generalizing start finish with
  | zero =>
    cases path with
    | nil v => exact ⟨(0, []), by simp [hitTable, get_ofFn_fin, terminal], Nat.zero_le _⟩
    | cons edge rest => simp [pathEdges] at within
  | succ limit ih =>
    by_cases start_terminal : goal start = true
    · exact ⟨(0, []), by simp [hitTable, get_ofFn_fin, start_terminal], Nat.zero_le _⟩
    · cases path with
      | nil v => exact False.elim (start_terminal terminal)
      | cons edge rest =>
        have shorter : (pathEdges rest).length ≤ limit := by simp [pathEdges] at within; omega
        obtain ⟨suffix, returned, minimal⟩ := ih rest terminal shorter
        let candidates := (outgoing (G.source edge)).filterMap (fun e =>
          G.extendHit weight (G.hitTable outgoing weight goal limit) e.val)
        have member : (weight edge + suffix.1, edge :: suffix.2) ∈ candidates := by
          apply List.mem_filterMap.mpr
          exact ⟨⟨edge, rfl⟩, complete edge, by simp [extendHit, returned]⟩
        have best_exists := List.isSome_minOn?_of_mem (f := Prod.fst) member
        have best_minimal := List.apply_get_minOn?_le_of_mem (f := Prod.fst) member
        cases best : candidates.minOn? Prod.fst with
        | none => simp [best] at best_exists
        | some result =>
          refine ⟨result, ?_, ?_⟩
          · simpa [hitTable, get_ofFn_fin, start_terminal, candidates] using best
          · simp only [best, Option.get_some] at best_minimal
            simp only [pathEdges, List.map_cons, List.sum_cons]
            exact Nat.le_trans best_minimal (Nat.add_le_add_left minimal _)

private def pathVertices {G : DirectedGraph V E} {x y : V} : G.Path x y → List V
  | .nil v => [v]
  | .cons edge rest => G.source edge :: pathVertices rest

private theorem path_vertices_length {G : DirectedGraph V E} {x y : V} (path : G.Path x y) :
    (pathVertices path).length = (pathEdges path).length + 1 := by
  induction path <;> simp_all [pathVertices, pathEdges]

private theorem path_suffix_of_vertex {G : DirectedGraph V E} {x y v : V}
    (path : G.Path x y) (member : v ∈ pathVertices path) :
    ∃ suffix : G.Path v y,
      (pathVertices suffix).Sublist (pathVertices path) ∧
        (pathEdges suffix).Sublist (pathEdges path) := by
  induction path with
  | nil x =>
    simp only [pathVertices, List.mem_singleton] at member
    subst v
    exact ⟨.nil x, .refl _, .refl _⟩
  | cons edge rest ih =>
    rcases List.mem_cons.mp member with equality | later
    · subst v
      exact ⟨.cons edge rest, .refl _, .refl _⟩
    · obtain ⟨suffix, vertices, edges⟩ := ih later
      exact ⟨suffix, vertices.cons _, edges.cons _⟩

private theorem path_remove_cycles {G : DirectedGraph V E} {x y : V} (path : G.Path x y) :
    ∃ simple : G.Path x y, (pathVertices simple).Nodup ∧
      (pathEdges simple).Sublist (pathEdges path) := by
  classical
  induction path with
  | nil x => exact ⟨.nil x, by simp [pathVertices], .refl _⟩
  | cons edge rest ih =>
    obtain ⟨suffix, distinct, shortened⟩ := ih
    by_cases repeated : G.source edge ∈ pathVertices suffix
    · obtain ⟨simple, vertices, edges⟩ := path_suffix_of_vertex suffix repeated
      exact ⟨simple, vertices.nodup distinct, (edges.trans shortened).cons _⟩
    · exact ⟨.cons edge suffix, List.nodup_cons.mpr ⟨repeated, distinct⟩, shortened.cons_cons _⟩

private theorem nat_sum_le_of_sublist {xs ys : List Nat} (included : xs.Sublist ys) :
    xs.sum ≤ ys.sum := by
  induction included with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

theorem finite_hit_global_minimal {n : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (complete : ∀ e : E, ⟨e, rfl⟩ ∈ outgoing (G.source e))
    (weight : E → Nat) (goal : Fin n → Bool) {start finish : Fin n}
    (path : G.Path start finish) (terminal : goal finish = true) :
    ∃ result, (G.hitTable outgoing weight goal (n - 1)).get start = some result ∧
      result.1 ≤ ((pathEdges path).map weight).sum := by
  obtain ⟨simple, distinct, included⟩ := path_remove_cycles path
  have length := distinct.length_le_of_subset (l₂ := List.finRange n) fun v _ =>
    List.mem_finRange v
  rw [List.length_finRange, path_vertices_length] at length
  obtain ⟨result, found, comparison⟩ :=
    G.finite_hit_complete_and_minimal outgoing complete weight goal (n - 1) simple terminal
      (by omega)
  exact ⟨result, found, Nat.le_trans comparison (nat_sum_le_of_sublist (included.map weight))⟩

private def budgetIndex {n cap : Nat} (v : Fin n) (remaining : Fin (cap + 1)) :
    Fin (n * (cap + 1)) :=
  ⟨v.val * (cap + 1) + remaining.val, by
    have next := Nat.mul_le_mul_right (cap + 1) (Nat.succ_le_of_lt v.isLt)
    rw [Nat.succ_mul] at next
    have inside := remaining.isLt
    omega⟩

private def baseVertex {n cap : Nat} (i : Fin (n * (cap + 1))) : Fin n :=
  ⟨i.val / (cap + 1), (Nat.div_lt_iff_lt_mul (by omega)).mpr i.isLt⟩

private def budgetRemaining {n cap : Nat} (i : Fin (n * (cap + 1))) : Fin (cap + 1) :=
  ⟨i.val % (cap + 1), Nat.mod_lt _ (by omega)⟩

@[simp] private theorem baseVertex_index {n cap : Nat} (v : Fin n) (r : Fin (cap + 1)) :
    baseVertex (budgetIndex v r) = v := by
  apply Fin.ext
  change (v.val * (cap + 1) + r.val) / (cap + 1) = v.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt r.isLt, Nat.zero_add]

@[simp] private theorem budgetRemaining_index {n cap : Nat} (v : Fin n) (r : Fin (cap + 1)) :
    budgetRemaining (budgetIndex v r) = r := by
  apply Fin.ext
  exact (Nat.mul_add_mod_self_right _ _ _).trans (Nat.mod_eq_of_lt r.isLt)

private theorem budgetIndex_parts {n cap : Nat} (i : Fin (n * (cap + 1))) :
    budgetIndex (baseVertex i) (budgetRemaining i) = i := by
  apply Fin.ext
  change i.val / (cap + 1) * (cap + 1) + i.val % (cap + 1) = i.val
  rw [Nat.mul_comm (i.val / _), Nat.add_comm]
  exact Nat.mod_add_div _ _

/-- Replay the resource transitions along an original path. -/
def resourceTrace {R : Type _} (advance : R → E → Option R) : R → List E → Option R
  | state, [] => some state
  | state, edge :: rest => (advance state edge).bind (fun next => resourceTrace advance next rest)

theorem resourceTrace_dominates {R : Type _} (advance : R → E → Option R)
    (dominatedBy : R → R → Prop)
    (step : ∀ {small large after : R} {edge : E}, dominatedBy small large →
      advance small edge = some after →
      ∃ afterLarge, advance large edge = some afterLarge ∧ dominatedBy after afterLarge)
    {small large finish : R} {edges : List E} (initial : dominatedBy small large)
    (replay : resourceTrace advance small edges = some finish) :
    ∃ finishLarge, resourceTrace advance large edges = some finishLarge ∧
      dominatedBy finish finishLarge := by
  induction edges generalizing small large finish with
  | nil =>
    have same : small = finish := Option.some.inj replay
    subst finish
    exact ⟨large, rfl, initial⟩
  | cons edge rest ih =>
    cases smallStep : advance small edge with
    | none => simp [resourceTrace, smallStep] at replay
    | some after =>
      obtain ⟨afterLarge, largeStep, nextDominance⟩ := step initial smallStep
      have tail : resourceTrace advance after rest = some finish := by
        simpa [resourceTrace, smallStep] using replay
      obtain ⟨finishLarge, lifted, dominates⟩ := ih nextDominance tail
      exact ⟨finishLarge, by simpa [resourceTrace, largeStep] using lifted, dominates⟩

private structure BudgetMove {cap : Nat}
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1))) where
  edge : E
  before : Fin (cap + 1)
  after : Fin (cap + 1)
  step : advance before edge = some after

private def budgetGraph {n cap : Nat} (G : DirectedGraph (Fin n) E)
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1))) :
    DirectedGraph (Fin (n * (cap + 1))) (BudgetMove advance) where
  source := fun move => budgetIndex (G.source move.edge) move.before
  target := fun move => budgetIndex (G.target move.edge) move.after

private def budgetOutgoing {n cap : Nat} {G : DirectedGraph (Fin n) E}
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1)))
    (i : Fin (n * (cap + 1))) : List {e : BudgetMove advance // (G.budgetGraph advance).source e = i} :=
  (outgoing (baseVertex i)).filterMap fun edge =>
    match checked : advance (budgetRemaining i) edge.val with
    | some next => some ⟨⟨edge.val, budgetRemaining i, next, checked⟩, by
        change budgetIndex (G.source edge.val) (budgetRemaining i) = i
        rw [edge.property, budgetIndex_parts]⟩
    | none => none

private theorem budgetOutgoing_complete {n cap : Nat} {G : DirectedGraph (Fin n) E}
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (complete : ∀ e : E, ⟨e, rfl⟩ ∈ outgoing (G.source e))
    {advance : Fin (cap + 1) → E → Option (Fin (cap + 1))} (move : BudgetMove advance) :
    ⟨move, rfl⟩ ∈ budgetOutgoing outgoing advance ((G.budgetGraph advance).source move) := by
  have listed {v : Fin n} (h : G.source move.edge = v) : ⟨move.edge, h⟩ ∈ outgoing v := by
    subst v
    exact complete move.edge
  apply List.mem_filterMap.mpr
  refine ⟨⟨move.edge, by simp [budgetGraph]⟩, listed _, ?_⟩
  rcases move with ⟨edge, before, next, step⟩
  simp only [budgetGraph]
  have actual : advance (budgetRemaining (budgetIndex (G.source edge) before)) edge = some next :=
    by simpa only [budgetRemaining_index] using step
  split
  · rename_i selected observation
    have same := Option.some.inj (observation.symm.trans actual)
    subst selected
    simp only [budgetRemaining_index]
  · rename_i observation
    rw [actual] at observation
    contradiction

private def cacheOutgoing {n : Nat} {G : DirectedGraph (Fin n) E}
    (outgoing : ∀ v, List {e : E // G.source e = v}) :
    ∀ v, List {e : E // G.source e = v} :=
  let rows := Vector.ofFn (fun v => (⟨v, outgoing v⟩ : Σ v, List {e : E // G.source e = v}))
  fun v =>
    let row := rows.get v
    have same : row.1 = v := congrArg Sigma.fst (get_ofFn_fin _ v)
    same ▸ row.2

private theorem cacheOutgoing_eq {n : Nat} {G : DirectedGraph (Fin n) E}
    (outgoing : ∀ v, List {e : E // G.source e = v}) :
    cacheOutgoing outgoing = outgoing := by
  funext v
  have read (row : Σ i, List {e : E // G.source e = i})
      (same : row.1 = v) (correct : row = ⟨v, outgoing v⟩) :
      (same ▸ row.2) = outgoing v := by
    subst row
    rfl
  exact read _ _ (get_ofFn_fin _ v)

/-- Minimum cost over a step-limited search with an exact finite resource state. -/
def constrainedHit {n cap : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1)))
    (weight : E → Nat) (goal : Fin n → Fin (cap + 1) → Bool) (initial : Fin (cap + 1))
    (limit : Nat) (start : Fin n) : Option (Nat × List E) :=
  let graph := G.budgetGraph advance
  let edges := cacheOutgoing (budgetOutgoing (cacheOutgoing outgoing) advance)
  let table := graph.hitTable edges (fun e => weight e.edge)
    (fun i => goal (baseVertex i) (budgetRemaining i)) limit
  (table.get (budgetIndex start initial)).map fun result =>
    (result.1, result.2.map BudgetMove.edge)

private theorem pathEdges_cast_start {G : DirectedGraph V E} {x x' y : V}
    (move : x = x') (path : G.Path x y) :
    pathEdges (move ▸ path : G.Path x' y) = pathEdges path := by
  cases move
  rfl

private theorem budget_path_project {n cap : Nat} {G : DirectedGraph (Fin n) E}
    {advance : Fin (cap + 1) → E → Option (Fin (cap + 1))}
    {start finish : Fin (n * (cap + 1))}
    (path : (G.budgetGraph advance).Path start finish) :
    ∃ projected : G.Path (baseVertex start) (baseVertex finish),
      pathEdges projected = (pathEdges path).map BudgetMove.edge ∧
      resourceTrace advance (budgetRemaining start) (pathEdges projected) =
        some (budgetRemaining finish) := by
  induction path with
  | nil => exact ⟨.nil _, rfl, rfl⟩
  | cons move tail ih =>
    obtain ⟨projected, recorded, replay⟩ := ih
    have sourceEq : G.source move.edge = baseVertex ((G.budgetGraph advance).source move) :=
      by simp [budgetGraph]
    have targetEq : baseVertex ((G.budgetGraph advance).target move) = G.target move.edge :=
      by simp [budgetGraph]
    let alignedTail := (targetEq ▸ projected : G.Path (G.target move.edge) (baseVertex _))
    let head := (Path.cons move.edge alignedTail)
    refine ⟨sourceEq ▸ head, ?_, ?_⟩
    · rw [pathEdges_cast_start]
      change move.edge :: pathEdges alignedTail = move.edge :: (pathEdges tail).map BudgetMove.edge
      rw [pathEdges_cast_start, recorded]
    · rw [pathEdges_cast_start]
      change resourceTrace advance _ (move.edge :: pathEdges alignedTail) = _
      rw [pathEdges_cast_start]
      simp only [resourceTrace, budgetGraph, budgetRemaining_index, move.step, Option.bind]
      simpa only [budgetGraph, budgetRemaining_index] using replay

private theorem budget_path_lift {n cap : Nat} {G : DirectedGraph (Fin n) E}
    {advance : Fin (cap + 1) → E → Option (Fin (cap + 1))}
    {start finish : Fin n} (path : G.Path start finish) (initial final : Fin (cap + 1))
    (replays : resourceTrace advance initial (pathEdges path) = some final) :
    ∃ lifted : (G.budgetGraph advance).Path (budgetIndex start initial) (budgetIndex finish final),
      (pathEdges lifted).map BudgetMove.edge = pathEdges path := by
  induction path generalizing initial with
  | nil =>
    have same : initial = final := Option.some.inj replays
    subst final
    exact ⟨.nil _, rfl⟩
  | cons edge rest ih =>
    cases next : advance initial edge with
    | none => simp [pathEdges, resourceTrace, next] at replays
    | some after =>
      have replayRest : resourceTrace advance after (pathEdges rest) = some final := by
        simpa [pathEdges, resourceTrace, next] using replays
      obtain ⟨suffix, copied⟩ := ih after replayRest
      let move : BudgetMove advance := ⟨edge, initial, after, next⟩
      refine ⟨.cons move suffix, ?_⟩
      change edge :: (pathEdges suffix).map BudgetMove.edge = edge :: pathEdges rest
      exact congrArg (edge :: ·) copied

theorem constrained_hit_sound {n cap : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1)))
    (weight : E → Nat) (goal : Fin n → Fin (cap + 1) → Bool) (initial : Fin (cap + 1))
    (limit : Nat) (start : Fin n) (cost : Nat) (edges : List E)
    (found : G.constrainedHit outgoing advance weight goal initial limit start = some (cost, edges)) :
    ∃ finish : Fin n, ∃ path : G.Path start finish, ∃ final : Fin (cap + 1),
      goal finish final = true ∧ (pathEdges path).length ≤ limit ∧
      resourceTrace advance initial (pathEdges path) = some final ∧
      pathEdges path = edges ∧ ((pathEdges path).map weight).sum = cost := by
  unfold constrainedHit at found
  simp only [cacheOutgoing_eq] at found
  obtain ⟨⟨charged, moves⟩, selected, result⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨finish, lifted, terminal, length, desc, chargedEq⟩ :=
    (G.budgetGraph advance).finite_hit_sound (budgetOutgoing outgoing advance)
      (fun e => weight e.edge) (fun i => goal (baseVertex i) (budgetRemaining i)) limit
      (budgetIndex start initial) charged moves selected
  obtain ⟨path, readback, replay⟩ := budget_path_project lifted
  let aligned := (baseVertex_index start initial ▸ path : G.Path start (baseVertex finish))
  have alignedEdges : pathEdges aligned = (pathEdges lifted).map BudgetMove.edge :=
    (pathEdges_cast_start _ _).trans readback
  simp only [Prod.mk.injEq] at result
  refine ⟨baseVertex finish, aligned, budgetRemaining finish, terminal, ?_, ?_, ?_, ?_⟩
  · simpa only [alignedEdges, List.length_map] using length
  · rw [pathEdges_cast_start]
    simpa only [budgetRemaining_index] using replay
  · rw [alignedEdges, desc, result.2]
  · simpa only [alignedEdges, List.map_map, Function.comp_def, result.1] using chargedEq

theorem constrained_hit_complete_and_minimal {n cap : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (complete : ∀ e : E, ⟨e, rfl⟩ ∈ outgoing (G.source e))
    (advance : Fin (cap + 1) → E → Option (Fin (cap + 1)))
    (weight : E → Nat) (goal : Fin n → Fin (cap + 1) → Bool) (initial final : Fin (cap + 1))
    (limit : Nat) {start finish : Fin n} (path : G.Path start finish)
    (terminal : goal finish final = true) (within : (pathEdges path).length ≤ limit)
    (replay : resourceTrace advance initial (pathEdges path) = some final) :
    ∃ result, G.constrainedHit outgoing advance weight goal initial limit start = some result ∧
      result.1 ≤ ((pathEdges path).map weight).sum := by
  obtain ⟨lifted, copies⟩ := budget_path_lift path initial final replay
  have length := congrArg List.length copies
  simp only [List.length_map] at length
  obtain ⟨⟨cost, moves⟩, selected, comparison⟩ :=
    (G.budgetGraph advance).finite_hit_complete_and_minimal
      (budgetOutgoing outgoing advance) (budgetOutgoing_complete outgoing complete)
      (fun e => weight e.edge) (fun i => goal (baseVertex i) (budgetRemaining i)) limit lifted
      (by simpa only [baseVertex_index, budgetRemaining_index]) (by omega)
  refine ⟨(cost, moves.map BudgetMove.edge), ?_, ?_⟩
  · dsimp only [constrainedHit]
    simp only [cacheOutgoing_eq, selected, Option.map_some]
  · rw [← copies, List.map_map]
    exact comparison

def resourceCapacity : List Nat → Nat
  | [] => 1
  | cap :: caps => (cap + 1) * resourceCapacity caps

private theorem resourceCapacity_positive (caps : List Nat) : 0 < resourceCapacity caps := by
  induction caps with
  | nil => decide
  | cons cap caps ih => exact Nat.mul_pos (Nat.succ_pos cap) ih

def resourceDigits : List Nat → Nat → List Nat
  | [], _ => []
  | cap :: caps, code => code % (cap + 1) :: resourceDigits caps (code / (cap + 1))

/-- Subtract each resource in its own coordinate, rejecting a deficient digit. -/
def spendResourceCode : List Nat → Nat → List Nat → Option Nat
  | [], 0, [] => some 0
  | cap :: caps, code, use :: uses => do
    let remaining := code % (cap + 1)
    if use ≤ remaining then
      let tail ← spendResourceCode caps (code / (cap + 1)) uses
      return (cap + 1) * tail + (remaining - use)
    else none
  | _, _, _ => none

theorem full_resource_digits (caps : List Nat) :
    resourceDigits caps (resourceCapacity caps - 1) = caps := by
  induction caps with
  | nil => rfl
  | cons cap caps ih =>
    let tail := resourceCapacity caps
    have tail_positive : 0 < tail := resourceCapacity_positive caps
    have radix : 0 < cap + 1 := Nat.succ_pos cap
    have cover : tail = (tail - 1) + 1 := by omega
    have encoded : (cap + 1) * tail - 1 = (cap + 1) * (tail - 1) + cap := by
      have product := congrArg ((cap + 1) * ·) cover
      simp only [Nat.mul_add, Nat.mul_one] at product
      omega
    change resourceDigits (cap :: caps) ((cap + 1) * tail - 1) = _
    rw [encoded]
    unfold resourceDigits
    simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Nat.lt_succ_self cap)]
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ radix,
      Nat.div_eq_of_lt (Nat.lt_succ_self cap), Nat.zero_add]
    exact congrArg (cap :: ·) ih

theorem spend_resources_sound {caps use : List Nat} {before remaining : Nat}
    (accepted : spendResourceCode caps before use = some remaining) :
    remaining < resourceCapacity caps ∧ use.length = caps.length ∧
      List.zipWith (· + ·) (resourceDigits caps remaining) use = resourceDigits caps before := by
  induction caps generalizing before remaining use with
  | nil =>
    cases before <;> cases use <;> simp [spendResourceCode, resourceCapacity, resourceDigits] at accepted ⊢
    subst remaining
    decide
  | cons cap caps ih =>
    cases use with
    | nil => simp [spendResourceCode] at accepted
    | cons use uses =>
      have radix : 0 < cap + 1 := Nat.succ_pos cap
      let digit := before % (cap + 1)
      have digit_inside : digit < cap + 1 := Nat.mod_lt before radix
      by_cases enough : use ≤ digit
      · cases checked : spendResourceCode caps (before / (cap + 1)) uses with
        | none => simp [spendResourceCode, show use ≤ before % (cap + 1) from enough, checked] at accepted
        | some tail =>
          have selected : (cap + 1) * tail + (digit - use) = remaining := by
            simpa [spendResourceCode, show use ≤ before % (cap + 1) from enough, checked] using accepted
          subst remaining
          obtain ⟨tail_inside, length, balances⟩ := ih checked
          have forward := Nat.mul_le_mul_left (cap + 1) (Nat.succ_le_of_lt tail_inside)
          rw [Nat.mul_succ] at forward
          have rest_inside : digit - use < cap + 1 := by omega
          refine ⟨by change (cap + 1) * tail + (digit - use) < (cap + 1) * resourceCapacity caps
                     omega, by simp [length], ?_⟩
          unfold resourceDigits
          rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt rest_inside]
          rw [Nat.add_comm ((cap + 1) * tail), Nat.add_mul_div_left _ _ radix,
            Nat.div_eq_of_lt rest_inside, Nat.zero_add]
          rw [List.zipWith_cons_cons, Nat.sub_add_cancel enough, balances]
      · simp [spendResourceCode, show ¬ use ≤ before % (cap + 1) from enough] at accepted

theorem spend_resources_complete {caps use : List Nat} {before : Nat}
    (in_space : before < resourceCapacity caps) (aligned : use.length = caps.length)
    (fits : (List.zipWith (fun u r => decide (u ≤ r)) use (resourceDigits caps before)).all id = true) :
    ∃ next, spendResourceCode caps before use = some next := by
  induction caps generalizing before use with
  | nil =>
    have zero : before = 0 := by simpa [resourceCapacity] using in_space
    have empty : use = [] := List.length_eq_zero_iff.mp aligned
    subst before
    subst use
    exact ⟨0, rfl⟩
  | cons cap caps ih =>
    cases use with
    | nil => simp at aligned
    | cons use uses =>
      simp only [resourceDigits, List.zipWith_cons_cons, List.all_cons, id_eq,
        Bool.and_eq_true, decide_eq_true_eq] at fits
      have tail_valid : before / (cap + 1) < resourceCapacity caps :=
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos cap)).mpr
          (by simpa [resourceCapacity, Nat.mul_comm] using in_space)
      obtain ⟨tail, accepted⟩ := ih tail_valid (by simpa using aligned) fits.2
      exact ⟨(cap + 1) * tail + (before % (cap + 1) - use),
        by simp [spendResourceCode, fits.1, accepted]⟩

def resourceAdvance (caps : List Nat) (allowed : E → Bool) (use : E → List Nat)
    (remaining : Fin (resourceCapacity caps - 1 + 1)) (edge : E) :
    Option (Fin (resourceCapacity caps - 1 + 1)) := do
  if allowed edge then
    match checked : spendResourceCode caps remaining.val (use edge) with
    | none => none
    | some next =>
      have bounded := (spend_resources_sound checked).1
      return ⟨next, by omega⟩
  else none

def resourceConstrainedHit {n : Nat} (G : DirectedGraph (Fin n) E)
    (outgoing : ∀ v, List {e : E // G.source e = v})
    (allowed : E → Bool) (weight : E → Nat) (use : E → List Nat)
    (goal : Fin n → List Nat → Bool) (caps : List Nat) (limit : Nat) (start : Fin n) :
    Option (Nat × List E) :=
  G.constrainedHit outgoing (resourceAdvance caps allowed use) weight
    (fun v resource => goal v (resourceDigits caps resource.val))
    ⟨resourceCapacity caps - 1, Nat.lt_succ_self _⟩ limit start

end DirectedGraph

private def refineOptimisticHit {Edge : Type _} [DecidableEq Edge]
    (search : (Edge → Bool) → Option (Nat × List Edge)) (verify : Edge → Bool)
    (fuel : Nat) (pending rejected : List Edge) (resume : Option (Nat × List Edge)) :
    Option (Nat × List Edge) :=
  let candidate := resume.orElse (fun _ => search (fun edge => decide (edge ∉ rejected)))
  match candidate with
  | none => none
  | some path =>
    match path.2.find? (fun edge => decide (edge ∈ pending)) with
    | none => some path
    | some edge =>
      match fuel with
      | 0 => none
      | next + 1 =>
        let rest := pending.filter (fun other => decide (other ≠ edge))
        if verify edge then refineOptimisticHit search verify next rest rejected (some path)
        else refineOptimisticHit search verify next rest (edge :: rejected) none

/-- Verify gates on the least-cost relaxed path. Reuse that path after a passing gate. -/
def optimisticHit {Edge : Type _} [DecidableEq Edge]
    (search : (Edge → Bool) → Option (Nat × List Edge)) (verify : Edge → Bool)
    (pending : List Edge) : Option (Nat × List Edge) :=
  refineOptimisticHit search verify pending.length pending [] none

theorem verified_relaxed_minimum {Path : Type _} (cost : Path → Nat)
    (exact relaxed : Path → Prop) (included : ∀ p, exact p → relaxed p)
    (candidate : Path) (verified : exact candidate)
    (optimal : ∀ p, relaxed p → cost candidate ≤ cost p) :
    exact candidate ∧ ∀ p, exact p → cost candidate ≤ cost p :=
  ⟨verified, fun p valid => optimal p (included p valid)⟩

private def blockGateGraph : DirectedGraph (Fin 5) (Fin 6) where
  source edge := match edge.val with
    | 1 => 1
    | 3 => 2
    | 5 => 4
    | _ => 0
  target edge := match edge.val with
    | 0 => 1
    | 2 => 2
    | 4 => 4
    | _ => 3

private def blockGateSearch (allowed : Fin 6 → Bool) : Option (Nat × List (Fin 6)) :=
  blockGateGraph.resourceConstrainedHit
    (fun v => (List.finRange 6).filterMap fun edge =>
      if source : blockGateGraph.source edge = v then some ⟨edge, source⟩ else none)
    allowed (fun edge => if edge.val < 2 then 1 else if edge.val < 4 then 2 else 0)
    (fun _ => [1]) (fun v _ => v == 3) [2] 2 0

private def blockGateResidual (edge : Fin 6) : Nat :=
  match edge.val with
  | 0 => 3
  | 2 => 1
  | 4 | 5 => 2
  | _ => 0

theorem block_gate_optimistic_example :
    blockGateSearch (fun _ => true) = some (0, [4, 5]) ∧
    blockGateSearch (fun edge => decide (blockGateResidual edge ≤ 1)) = some (4, [2, 3]) ∧
    optimisticHit blockGateSearch (fun edge => decide (blockGateResidual edge ≤ 1)) [1, 3, 5] =
      some (2, [0, 1]) := by
  decide +kernel

/-- The search interface supplied by one certified LHTS type on its task quotient. -/
structure LHTSFinite (n : Nat) (Edge : Type _) where
  graph : DirectedGraph (Fin n) Edge
  candidates : ∀ vertex, List {edge : Edge // graph.source edge = vertex}
  complete : ∀ edge : Edge, ⟨edge, rfl⟩ ∈ candidates (graph.source edge)
  legal : Edge → Bool
  cost : Edge → Nat
  consumption : Edge → List Nat
  terminal : Fin n → List Nat → Bool
  remainingLower : Fin n → List Nat → Nat
  lowerSound : ∀ (caps : List Nat) {start finish : Fin n}
    (path : graph.Path start finish)
    (before after : Fin (DirectedGraph.resourceCapacity caps - 1 + 1)),
    DirectedGraph.resourceTrace (DirectedGraph.resourceAdvance caps legal consumption)
        before (DirectedGraph.pathEdges path) = some after →
    terminal finish (DirectedGraph.resourceDigits caps after.val) = true →
    remainingLower start (DirectedGraph.resourceDigits caps before.val) ≤
      ((DirectedGraph.pathEdges path).map cost).sum

theorem LHTSFinite.prune {n : Nat} {Edge : Type _} (model : LHTSFinite n Edge)
    (caps : List Nat) {start finish : Fin n} (path : model.graph.Path start finish)
    (before after : Fin (DirectedGraph.resourceCapacity caps - 1 + 1))
    (replay : DirectedGraph.resourceTrace
      (DirectedGraph.resourceAdvance caps model.legal model.consumption) before
      (DirectedGraph.pathEdges path) = some after)
    (terminal : model.terminal finish (DirectedGraph.resourceDigits caps after.val) = true)
    (spent incumbent : Nat)
    (excluded : incumbent < spent + model.remainingLower start
      (DirectedGraph.resourceDigits caps before.val)) :
    incumbent < spent + ((DirectedGraph.pathEdges path).map model.cost).sum :=
  Nat.lt_of_lt_of_le excluded (Nat.add_le_add_left (model.lowerSound caps path before after replay terminal) _)

/-- The tag travels with the quotient vertex, remaining budget, and resulting edge type. -/
def tphHit {Tag : Type _} {n : Tag → Nat} {Edge : Tag → Type _}
    (models : ∀ tag, LHTSFinite (n tag) (Edge tag))
    (state : Σ tag, Fin (n tag) × List Nat) (limit : Nat) :
    Option (Nat × List (Edge state.1)) :=
  let model := models state.1
  model.graph.resourceConstrainedHit model.candidates model.legal model.cost model.consumption
    model.terminal state.2.2 limit state.2.1

private def strongestBetween {Result : Type _} (probe : Nat → Option Result)
    (lower upper : Nat) (witness : Result) : Nat × Result :=
  if _separated : lower + 1 < upper then
    let middle := lower + (upper - lower) / 2
    match probe middle with
    | none => strongestBetween probe lower middle witness
    | some found => strongestBetween probe middle upper found
  else (lower, witness)
termination_by upper - lower
decreasing_by all_goals omega

/-- Find the greatest feasible grade. A probe retains its least-cost witness. -/
def strongestBudgetHit {Result : Type _} (probe : Nat → Option Result)
    (cap : Nat) : Option (Nat × Result) := do
  let initial ← probe 0
  return strongestBetween probe 0 (cap + 1) initial

private theorem strongest_between_spec {Result : Type _} (probe : Nat → Option Result)
    (monotone : ∀ i j, i ≤ j → probe i = none → probe j = none)
    (cap lower upper : Nat) (witness : Result)
    (ordered : lower < upper) (capBound : upper ≤ cap + 1)
    (confirmed : probe lower = some witness)
    (excluded : ∀ grade, upper ≤ grade → grade ≤ cap → probe grade = none) :
    let best := strongestBetween probe lower upper witness
    best.1 ≤ cap ∧ probe best.1 = some best.2 ∧
      ∀ grade, grade ≤ cap → probe grade ≠ none → grade ≤ best.1 := by
  rw [strongestBetween]
  split
  · rename_i separated
    let middle := lower + (upper - lower) / 2
    change let best := match probe middle with
      | none => strongestBetween probe lower middle witness
      | some found => strongestBetween probe middle upper found
    best.1 ≤ cap ∧ probe best.1 = some best.2 ∧
      ∀ grade, grade ≤ cap → probe grade ≠ none → grade ≤ best.1
    have first : lower < middle := by dsimp [middle]; omega
    have second : middle < upper := by dsimp [middle]; omega
    cases checked : probe middle with
    | none =>
      simpa only [checked] using strongest_between_spec probe monotone cap lower middle witness
        first (by omega) confirmed (fun grade later _ => monotone middle grade later checked)
    | some found =>
      simpa only [checked] using strongest_between_spec probe monotone cap middle upper found
        second capBound checked excluded
  · rename_i adjacent
    refine ⟨by omega, confirmed, ?_⟩
    intro grade within feasible
    change grade ≤ lower
    by_cases included : grade ≤ lower
    · exact included
    · exact False.elim (feasible (excluded grade (by omega) within))
termination_by upper - lower
decreasing_by all_goals omega

theorem strongest_budget_hit_spec {Result : Type _} (probe : Nat → Option Result)
    (monotone : ∀ i j, i ≤ j → probe i = none → probe j = none)
    {cap grade : Nat} {witness : Result}
    (accepted : strongestBudgetHit probe cap = some (grade, witness)) :
    grade ≤ cap ∧ probe grade = some witness ∧
      ∀ other, other ≤ cap → probe other ≠ none → other ≤ grade := by
  cases first : probe 0 with
  | none => simp [strongestBudgetHit, first] at accepted
  | some initial =>
    have correct := strongest_between_spec probe monotone cap 0 (cap + 1) initial
      (Nat.zero_lt_succ _) (Nat.le_refl _) first (fun _ high low => by omega)
    simp [strongestBudgetHit, first] at accepted
    simpa only [accepted] using correct

theorem strongest_budget_hit_no_feasible {Result : Type _} (probe : Nat → Option Result)
    (monotone : ∀ i j, i ≤ j → probe i = none → probe j = none)
    {cap : Nat} (missed : strongestBudgetHit probe cap = none) (grade : Nat) :
    probe grade = none := by
  cases first : probe 0 with
  | none => exact monotone 0 grade (Nat.zero_le _) first
  | some initial => simp [strongestBudgetHit, first] at missed

def correction (a b : Nat) : Int × Int × Int :=
  ((a : Int) + b, -(a : Int), -(b : Int))

def sumCoordinates (v : Int × Int × Int) : Int := v.1 + v.2.1 + v.2.2

theorem joint_reachability_expansion (m : Nat) (positive : 0 < m) :
    (∀ a : Nat, correction a 0 ≠ correction 0 m) ∧
    (∀ k : Nat, k ≤ m → sumCoordinates (correction 0 k) = 0) ∧
    (∀ a b : Nat, correction a b = correction 0 m → m ≤ a + b) ∧
    sumCoordinates (correction 0 m) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a h
    have e := congrArg (fun t => t.2.2) h
    change -(0 : Int) = -(m : Int) at e
    omega
  · intro k _
    simp [sumCoordinates, correction]
  · intro a b h
    have e := congrArg (fun t => t.2.2) h
    change -(b : Int) = -(m : Int) at e
    omega
  · simp [sumCoordinates, correction]

end GAlgebra
