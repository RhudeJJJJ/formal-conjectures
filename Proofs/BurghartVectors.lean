import Proofs.BurghartAlgebra
import Proofs.BurghartIdeals
/-! # Verified coefficient lists, exhaustive leaf classes and path-union transport -/
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
namespace BurghartLists
open Finset
abbrev P := MvPolynomial (Fin 3) ℤ

def addList {α : Type*} (op : α → α → α) : List α → List α → List α
  | [],q => q
  | p,[] => p
  | a :: p,b :: q => op a b :: addList op p q

instance {α : Type*} (op : α → α → α) [Std.Associative op] : Std.Associative (addList op) := ⟨by
  intro p q r
  induction p generalizing q r with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      cases r with
      | nil => rfl
      | cons c r => simp only [addList,Std.Associative.assoc,ih]⟩
instance {α : Type*} (op : α → α → α) [Std.Commutative op] : Std.Commutative (addList op) := ⟨by
  intro p q
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => simp only [addList,Std.Commutative.comm,ih]⟩

noncomputable def eval {α : Type*} (f : α → P) (x : P) : List α → P
  | [] => 0
  | a :: p => f a + x * eval f x p

theorem eval_add {α : Type*} (op : α → α → α) (f : α → P) (x : P)
    (hf : ∀ a b, f (op a b) = f a + f b) (p q : List α) :
    eval f x (addList op p q) = eval f x p + eval f x q := by
  induction p generalizing q with
  | nil => simp [addList,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [addList,eval]
    | cons b q => simp only [addList,eval,hf,ih]; ring

def mono {α : Type*} (zero : α) (n : ℕ) (a : α) : List α := List.replicate n zero ++ [a]

theorem eval_mono {α : Type*} (zero : α) (f : α → P) (x : P) (hz : f zero = 0)
    (n : ℕ) (a : α) : eval f x (mono zero n a) = x^n * f a := by
  induction n with
  | zero => simp [mono,eval]
  | succ n ih =>
    simp only [mono,List.replicate_succ,List.cons_append,eval,hz,zero_add] at *
    rw [ih,pow_succ]
    ring

def trim {α : Type*} [DecidableEq α] (zero : α) : List α → List α
  | [] => []
  | a :: p => let q := trim zero p; if a = zero ∧ q = [] then [] else a :: q

theorem eval_trim {α : Type*} [DecidableEq α] (zero : α) (f : α → P) (x : P)
    (hz : f zero = 0) (p : List α) : eval f x (trim zero p) = eval f x p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change eval f x (if a = zero ∧ trim zero p = [] then [] else a :: trim zero p) = _
    by_cases h : a = zero ∧ trim zero p = []
    · rw [if_pos h]
      have hp : eval f x p = 0 := by rw [← ih,h.2]; rfl
      simp [eval,h.1,hz,hp]
    · rw [if_neg h]
      simp only [eval,ih]

theorem eval_map {α β : Type*} (g : α → β) (f : β → P) (h : α → P) (x : P)
    (he : ∀ a, f (g a) = h a) (p : List α) : eval f x (p.map g) = eval h x p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.map_cons,eval,he,ih]

abbrev add1 := addList (fun a b : ℤ => a+b)
abbrev add2 := addList add1
abbrev add3 := addList add2
abbrev V1 := List ℤ
abbrev V2 := List V1
abbrev V3 := List V2
noncomputable def eval1 : V1 → P := eval MvPolynomial.C (MvPolynomial.X 2)
noncomputable def eval2 : V2 → P := eval eval1 (MvPolynomial.X 1)
noncomputable def eval3 : V3 → P := eval eval2 (MvPolynomial.X 0)
theorem eval1_add (p q : V1) : eval1 (add1 p q) = eval1 p + eval1 q :=
  eval_add _ _ _ (fun a b => map_add MvPolynomial.C a b) p q
theorem eval2_add (p q : V2) : eval2 (add2 p q) = eval2 p + eval2 q :=
  eval_add _ _ _ eval1_add p q
theorem eval3_add (p q : V3) : eval3 (add3 p q) = eval3 p + eval3 q :=
  eval_add _ _ _ eval2_add p q

def norm1 (p : V1) := trim 0 p
def norm2 (p : V2) := trim [] (p.map norm1)
def norm3 (p : V3) := trim [] (p.map norm2)
theorem eval_norm1 (p : V1) : eval1 (norm1 p) = eval1 p :=
  eval_trim _ _ _ (map_zero MvPolynomial.C) p
theorem eval_norm2 (p : V2) : eval2 (norm2 p) = eval2 p := by
  rw [norm2,show eval2 = eval eval1 (MvPolynomial.X 1) from rfl,
    eval_trim [] _ _ rfl,eval_map norm1 _ _ _ eval_norm1]
theorem eval_norm3 (p : V3) : eval3 (norm3 p) = eval3 p := by
  rw [norm3,show eval3 = eval eval2 (MvPolynomial.X 0) from rfl,
    eval_trim [] _ _ rfl,eval_map norm2 _ _ _ eval_norm2]

def sum1 {α : Type*} (s : Finset α) (f : α → V1) : V1 := s.fold add1 [] f
def sum3 {α : Type*} (s : Finset α) (f : α → V3) : V3 := s.fold add3 [] f

theorem eval_fold {α β : Type*} (s : Finset α) (op : β → β → β)
    [Std.Associative op] [Std.Commutative op] (zero : β) (f : α → β) (e : β → P)
    (hz : e zero = 0) (ha : ∀ p q, e (op p q) = e p + e q) :
    e (s.fold op zero f) = ∑ a ∈ s, e (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert a s hn ih => simp only [Finset.fold_insert hn,Finset.sum_insert hn,ha,ih]

theorem eval_sum1 {α : Type*} (s : Finset α) (f : α → V1) : eval1 (sum1 s f) = ∑ a ∈ s,eval1 (f a) :=
  eval_fold s add1 [] f eval1 rfl eval1_add
theorem eval_sum3 {α : Type*} (s : Finset α) (f : α → V3) : eval3 (sum3 s f) = ∑ a ∈ s,eval3 (f a) :=
  eval_fold s add3 [] f eval3 rfl eval3_add

#print axioms eval_norm3
#print axioms eval_sum3
end BurghartLists

namespace BurghartCertificate
open Finset

def fastList (a : Fin 28 → Finset (Fin 28)) : List (Fin 28) → List (Finset (Fin 28))
  | [] => [∅]
  | v :: vs => fastList a vs ++ ((fastList a vs).filter (fun S => decide (a v ⊆ insert v S))).map (insert v)

theorem fastList_subset (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (S : Finset (Fin 28)) (h : S ∈ fastList a vs) : S ⊆ vs.toFinset := by
  induction vs generalizing S with
  | nil => simpa [fastList] using h
  | cons v vs ih =>
    simp only [fastList,List.mem_append,List.mem_map,List.mem_filter,decide_eq_true_eq] at h
    rcases h with h | ⟨R,⟨hR,_⟩,rfl⟩
    · exact (ih S h).trans (by simp)
    · simpa only [List.toFinset_cons] using insert_subset_insert v (ih R hR)

theorem fastList_nodup (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (hn : vs.Nodup) : (fastList a vs).Nodup := by
  induction vs with
  | nil => simp [fastList]
  | cons v vs ih =>
    have hv := (List.nodup_cons.mp hn).1
    have ih := ih (List.nodup_cons.mp hn).2
    have hnot : ∀ S ∈ fastList a vs, v ∉ S := by
      intro S hS hmem
      exact hv (List.mem_toFinset.mp (fastList_subset a vs S hS hmem))
    rw [fastList,List.nodup_append]
    refine ⟨ih,?_,?_⟩
    · apply List.Nodup.map_on _ (ih.filter _)
      intro R hR S hS he
      have hR' := (List.mem_filter.mp hR).1
      have hS' := (List.mem_filter.mp hS).1
      simpa only [Finset.erase_insert (hnot R hR'),Finset.erase_insert (hnot S hS')] using
        congrArg (fun S => S.erase v) he
    · intro S hS T hT he
      obtain ⟨R,_,rfl⟩ := List.mem_map.mp hT
      exact hnot S hS (he.symm ▸ mem_insert_self v R)

theorem mem_fastList (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28))
    (S : Finset (Fin 28)) : S ∈ fastList a vs ↔ S ∈ generated a vs := by
  induction vs generalizing S with
  | nil => simp [fastList,generated]
  | cons v vs ih =>
    simp only [fastList,generated,extend,List.mem_append,List.mem_map,List.mem_filter,
      decide_eq_true_eq,Finset.mem_union,Finset.mem_image,Finset.mem_filter,ih]

def fastFinset (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28)) (hn : vs.Nodup) :
    Finset (Finset (Fin 28)) := ⟨fastList a vs, by simpa using fastList_nodup a vs hn⟩

theorem generated_eq_fast (a : Fin 28 → Finset (Fin 28)) (vs : List (Fin 28)) (hn : vs.Nodup) :
    generated a vs = fastFinset a vs hn := by
  ext S
  change S ∈ generated a vs ↔ S ∈ fastList a vs
  exact (mem_fastList a vs S).symm

def admissiblesFast1 := fastFinset ancestors1 vertices1 (by decide +kernel)
def admissiblesFast2 := fastFinset ancestors2 vertices2 (by decide +kernel)

open scoped Classical in
theorem admissiblesFast1_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T1 0) = admissiblesFast1 := by
  rw [admissibles1_eq]
  exact generated_eq_fast _ _ _
open scoped Classical in
theorem admissiblesFast2_eq : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible T2 0) = admissiblesFast2 := by
  rw [admissibles2_eq]
  exact generated_eq_fast _ _ _

theorem admissiblesFast1_card : admissiblesFast1.card = 325 := by decide +kernel
#print axioms admissiblesFast1_card
theorem admissiblesFast2_card : admissiblesFast2.card = 325 := by decide +kernel
#print axioms admissiblesFast2_card

end BurghartCertificate

namespace BurghartLists
open BurghartCertificate Finset SimpleGraph

theorem eval_mono1 (k : ℕ) (c : ℤ) : eval1 (mono 0 k c) = MvPolynomial.C c * MvPolynomial.X (2:Fin 3)^k := by
  unfold eval1
  rw [eval_mono 0 _ _ (map_zero MvPolynomial.C)]
  ring
theorem eval_mono2 (k : ℕ) (p : V1) : eval2 (mono ([]:V1) k p) = MvPolynomial.X (1:Fin 3)^k * eval1 p :=
  eval_mono [] _ _ rfl k p
theorem eval_mono3 (k : ℕ) (p : V2) : eval3 (mono ([]:V2) k p) = MvPolynomial.X (0:Fin 3)^k * eval2 p :=
  eval_mono [] _ _ rfl k p

def fringeVec (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (v : Fin 28) : V1 :=
  sum1 (fringeCode (leavesCode G d) d v).powerset fun A =>
    if (pathsCode d v A).card = 0 then [] else
      mono 0 ((pathsCode d v A).card - 1) (-((-1:ℤ)^A.card))

def polyVec (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (C : Finset (Finset (Fin 28))) : V3 :=
  sum3 C fun S => mono ([]:V2) S.card (mono ([]:V1) ((boundaryCode G S).card - 1)
    (sum1 (boundaryCode G S) (fringeVec G d)))

open scoped Classical in
theorem m_eq_vec (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (r : Fin 28 → Fin 28 → List (Fin 28)) (hr : RoutesOK G r) (ht : G.IsTree)
    (C : Finset (Finset (Fin 28)))
    (hC : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible G 0) = C) :
    Burghart.MPolynomial.mPolynomial G 0 = eval3 (polyVec G (distanceCode r) C) := by
  classical
  unfold Burghart.MPolynomial.mPolynomial polyVec
  rw [hC,eval_sum3]
  apply Finset.sum_congr rfl
  intro S _
  rw [boundary_eq_code G S,eval_mono3,eval_mono2,eval_sum1,← mul_assoc]
  apply congrArg (fun p : P => MvPolynomial.X (0:Fin 3)^S.card *
    MvPolynomial.X (1:Fin 3)^((boundaryCode G S).card - 1) * p)
  apply Finset.sum_congr rfl
  intro v _
  rw [fringe_expanded,fringe_eq_code G r hr ht v]
  unfold fringeVec
  rw [eval_sum1]
  apply Finset.sum_congr rfl
  intro A _
  rw [paths_eq_code G r hr ht v A]
  by_cases hA : (pathsCode (distanceCode r) v A).card = 0
  · simp [hA,eval1,eval]
  · simp only [hA,if_false,eval_mono1]

#print axioms m_eq_vec



def polyOf (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (C : Finset (Finset (Fin 28))) (f : Fin 28 → V1) : V3 :=
  sum3 C fun S => mono ([]:V2) S.card (mono ([]:V1) ((boundaryCode G S).card - 1)
    (sum1 (boundaryCode G S) f))

theorem eval_polyOf_congr (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (C : Finset (Finset (Fin 28))) (f g : Fin 28 → V1)
    (h : ∀ v, eval1 (f v) = eval1 (g v)) : eval3 (polyOf G C f) = eval3 (polyOf G C g) := by
  classical
  unfold polyOf
  rw [eval_sum3,eval_sum3]
  apply Finset.sum_congr rfl
  intro S _
  rw [eval_mono3,eval_mono3,eval_mono2,eval_mono2,eval_sum1,eval_sum1]
  simp only [h]

open scoped Classical in
theorem m_eq_table (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (r : Fin 28 → Fin 28 → List (Fin 28)) (hr : RoutesOK G r) (ht : G.IsTree)
    (C : Finset (Finset (Fin 28)))
    (hC : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible G 0) = C)
    (d : Fin 28 → Fin 28 → ℕ) (hd : distanceCode r = d) (f : Fin 28 → V1)
    (hf : ∀ v, norm1 (fringeVec G d v) = f v) :
    Burghart.MPolynomial.mPolynomial G 0 = eval3 (polyOf G C f) := by
  rw [m_eq_vec G r hr ht C hC,hd]
  exact eval_polyOf_congr G C _ f (fun v => (eval_norm1 _).symm.trans (congrArg eval1 (hf v)))
#print axioms m_eq_table


def leafMask (A : Finset (Fin 28)) : Fin 16 :=
  ⟨(if 6 ∈ A then 1 else 0) + (if 7 ∈ A then 2 else 0) +
    (if 8 ∈ A then 4 else 0) + (if 10 ∈ A then 8 else 0), by split_ifs <;> omega⟩

def fringePart (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (v : Fin 28) (i : Fin 16) : V1 :=
  sum1 ((fringeCode (leavesCode G d) d v).powerset.filter (fun A => leafMask A = i)) fun A =>
    if (pathsCode d v A).card = 0 then [] else
      mono 0 ((pathsCode d v A).card - 1) (-((-1:ℤ)^A.card))

theorem eval_fringe_parts (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (v : Fin 28) :
    eval1 (fringeVec G d v) = ∑ i : Fin 16, eval1 (fringePart G d v i) := by
  classical
  unfold fringeVec fringePart
  simp_rw [eval_sum1]
  exact (Finset.sum_fiberwise _ leafMask _).symm

open scoped Classical in
theorem m_eq_table_eval (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (r : Fin 28 → Fin 28 → List (Fin 28)) (hr : RoutesOK G r) (ht : G.IsTree)
    (C : Finset (Finset (Fin 28)))
    (hC : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible G 0) = C)
    (d : Fin 28 → Fin 28 → ℕ) (hd : distanceCode r = d) (f : Fin 28 → V1)
    (hf : ∀ v, eval1 (fringeVec G d v) = eval1 (f v)) :
    Burghart.MPolynomial.mPolynomial G 0 = eval3 (polyOf G C f) := by
  rw [m_eq_vec G r hr ht C hC,hd]
  exact eval_polyOf_congr G C _ f hf
#print axioms eval_fringe_parts
#print axioms m_eq_table_eval


theorem eval_fringe_from_parts (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (v : Fin 28) (f : Fin 16 → V1) (p : V1)
    (hf : ∀ i, norm1 (fringePart G d v i) = f i) (hs : norm1 (sum1 univ f) = p) :
    eval1 (fringeVec G d v) = eval1 p := by
  rw [eval_fringe_parts]
  calc
    ∑ i : Fin 16, eval1 (fringePart G d v i) = ∑ i : Fin 16, eval1 (f i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (eval_norm1 _).symm.trans (congrArg eval1 (hf i))
    _ = eval1 (sum1 univ f) := (eval_sum1 _ _).symm
    _ = eval1 p := (eval_norm1 _).symm.trans (congrArg eval1 hs)
#print axioms eval_fringe_from_parts


def pathSet (d : Fin 28 → Fin 28 → ℕ) (v l : Fin 28) : Finset (Fin 28) :=
  Finset.univ.filter (fun w => d v w + d w l = d v l)

theorem pathsCode_eq_union (d : Fin 28 → Fin 28 → ℕ) (v : Fin 28) (A : Finset (Fin 28)) :
    pathsCode d v A = A.biUnion (pathSet d v) := by
  classical
  ext w
  simp [pathsCode,pathSet]

def fastRootPart (L : Finset (Fin 28)) (p : Fin 28 → Finset (Fin 28)) (i : Fin 16) : V1 :=
  sum1 (L.powerset.filter (fun A => leafMask A = i)) fun A =>
    if (A.biUnion p).card = 0 then [] else
      mono 0 ((A.biUnion p).card - 1) (-((-1:ℤ)^A.card))

theorem fringePart_root_eq_fast (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (d : Fin 28 → Fin 28 → ℕ) (L : Finset (Fin 28)) (p : Fin 28 → Finset (Fin 28))
    (hL : fringeCode (leavesCode G d) d 0 = L) (hp : pathSet d 0 = p) (i : Fin 16) :
    fringePart G d 0 i = fastRootPart L p i := by
  classical
  unfold fringePart fastRootPart
  rw [hL]
  simp_rw [pathsCode_eq_union,hp]
#print axioms fringePart_root_eq_fast

end BurghartLists
