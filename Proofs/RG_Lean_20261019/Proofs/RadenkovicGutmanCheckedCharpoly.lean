/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCheckedRoots
import Proofs.RadenkovicGutmanSpectral
import Mathlib.LinearAlgebra.Matrix.Block

/-! Rational LU certificates and complete characteristic-polynomial identities.
An n by n matrix is checked at n+1 distinct rational arguments. Degree bounds
then identify the entire characteristic polynomial. The graph encoding uses
the actual adjacency relation and its exact row sums. -/
namespace Gebendorfer.RadenkovicGutman.CheckedCharpoly
open Matrix Polynomial Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

def acceptsLU {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℚ) (value : ℚ) : Bool :=
  decide ((∀ i j, A i j = ∑ k, L i k * U k j) ∧
    (∀ i j, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
    (∀ i j, j < i → U i j = 0) ∧ (∏ i, U i i) = value)

theorem determinant_of_acceptsLU {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℚ)
    (value : ℚ) (h : acceptsLU A L U value=true) : A.det=value := by
  obtain ⟨ha,hl,hd,hu,hv⟩ := of_decide_eq_true h
  have he : A=L*U := by ext i j; exact ha i j
  have hL : L.IsLowerTriangular := fun _ _ hij => hl _ _ hij
  have hU : U.IsUpperTriangular := fun _ _ hij => hu _ _ hij
  have hldet : L.det=1 := by rw [Matrix.det_of_isLowerTriangular L hL]; simp [hd]
  rw [he,Matrix.det_mul,hldet,one_mul,Matrix.det_of_isUpperTriangular hU]
  exact hv

theorem real_determinant_of_acceptsLU {n : ℕ} (A L U : Matrix (Fin n) (Fin n) ℚ)
    (value : ℚ) (h : acceptsLU A L U value=true) :
    (A.map (Rat.castHom ℝ)).det=(value : ℝ) := by
  calc
    _ = (Rat.castHom ℝ) A.det := ((Rat.castHom ℝ).map_det A).symm
    _ = _ := by rw [determinant_of_acceptsLU A L U value h]; rfl

def sample {n : ℕ} (k : Fin (n+1)) : ℚ := -((k.val : ℚ)+1)
def shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : ℚ) :
    Matrix (Fin n) (Fin n) ℚ := x • 1-A

theorem characteristic_polynomial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (cs : List ℚ) (hlen : cs.length≤n+1)
    (L U : Fin (n+1) → Matrix (Fin n) (Fin n) ℚ)
    (hc : ∀ k, acceptsLU (shifted A (sample k)) (L k) (U k)
      (CheckedRoots.eval cs (sample k))=true) :
    (A.map (Rat.castHom ℝ)).charpoly=CheckedRoots.polynomial cs := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
    (f := fun k : Fin (n+1) => (sample k : ℝ))
  · intro i j h
    change (sample i : ℝ) = (sample j : ℝ) at h
    apply Fin.ext
    have he : (i.val : ℚ)=(j.val : ℚ) := by
      have hh : sample i=sample j := Rat.cast_injective h
      dsimp only [sample] at hh
      linarith
    exact_mod_cast he
  · intro k
    rw [Matrix.eval_charpoly,← CheckedRoots.eval_cast]
    have h := real_determinant_of_acceptsLU _ _ _ _ (hc k)
    have he : (shifted A (sample k)).map (Rat.castHom ℝ)=
        (sample k : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)-A.map (Rat.castHom ℝ) := by
      ext i j
      by_cases hij : i = j <;>
        simp [shifted,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,hij]
    rw [he] at h
    simpa only [Matrix.smul_one_eq_diagonal,Matrix.scalar_apply] using h
  · have hp := CheckedRoots.degree_bound cs
    have hm := Matrix.charpoly_natDegree_eq_dim (A.map (Rat.castHom ℝ))
    simp only [Fintype.card_fin] at hm ⊢
    omega

def laplacian {n : ℕ} (adj : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (if i=j then ∑ k, if adj i k=true then 1 else 0 else 0)-
    (if adj i j=true then 1 else 0)

theorem laplacian_map {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (laplacian (fun i j => decide (G.Adj i j))).map (Rat.castHom ℝ)=G.lapMatrix ℝ := by
  have hd (i : Fin n) : (G.degree i : ℝ)=∑ j : Fin n, if G.Adj i j then 1 else 0 :=
    G.degree_eq_sum_if_adj i
  ext i j
  by_cases hij : i = j <;> by_cases ha : G.Adj i j <;>
    simp [laplacian,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,SimpleGraph.adjMatrix,
      Matrix.map_apply,Matrix.sub_apply,Matrix.diagonal_apply,hd,hij,ha]

theorem graph_characteristic_polynomial {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (cs : List ℚ) (hlen : cs.length≤n+1)
    (L U : Fin (n+1) → Matrix (Fin n) (Fin n) ℚ)
    (hc : ∀ k, acceptsLU (shifted (laplacian (fun i j => decide (G.Adj i j))) (sample k))
      (L k) (U k) (CheckedRoots.eval cs (sample k))=true) :
    (G.lapMatrix ℝ).charpoly=CheckedRoots.polynomial cs := by
  rw [← laplacian_map G]
  exact characteristic_polynomial _ cs hlen L U hc

def controlMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![1,-1;-1,1]
def controlL (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1,0;1/(sample k-1),1]
def controlU (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![sample k-1,1;0,(sample k-1)-1/(sample k-1)]
theorem control_accepts : ∀ k : Fin 3,
    acceptsLU (shifted controlMatrix (sample k)) (controlL k) (controlU k)
      (CheckedRoots.eval [0,-2,1] (sample k))=true := by decide +kernel
theorem control_charpoly :
    (controlMatrix.map (Rat.castHom ℝ)).charpoly=CheckedRoots.polynomial [0,-2,1] :=
  characteristic_polynomial _ _ (by decide) controlL controlU control_accepts
theorem wrong_factor_rejected :
    acceptsLU (!![-2,1;1,-2]) (!![1,0;-1/2,1]) (!![-2,1;0,-2]) 3=false := by
  decide +kernel
theorem singular_control :
    acceptsLU (!![1,1;1,1]) (!![1,0;1,1]) (!![1,1;0,0]) 0=true := by decide +kernel

#print axioms determinant_of_acceptsLU
#print axioms real_determinant_of_acceptsLU
#print axioms characteristic_polynomial
#print axioms laplacian_map
#print axioms graph_characteristic_polynomial
#print axioms control_accepts
#print axioms control_charpoly
#print axioms wrong_factor_rejected
#print axioms singular_control
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.CheckedCharpoly
