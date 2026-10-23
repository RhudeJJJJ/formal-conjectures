import Proofs.BurghartRep

/-! # BurghartAlgebra
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000
namespace BurghartPolynomial
open Finset
theorem quotient_expansion {α : Type*} (s : Finset α) (c : α → ℤ) (k : α → ℕ) :
    (1 - ∑ a ∈ s, Polynomial.C (c a) * Polynomial.X ^ k a).divX.eval₂
      (Int.castRingHom _) (MvPolynomial.X (2:Fin 3)) =
      ∑ a ∈ s, if k a = 0 then (0 : MvPolynomial (Fin 3) ℤ)
        else MvPolynomial.C (-(c a)) * MvPolynomial.X (2:Fin 3) ^ (k a - 1) := by
  classical
  have hd : (1 - ∑ a ∈ s, Polynomial.C (c a) * Polynomial.X ^ k a).divX =
      -(∑ a ∈ s, if k a = 0 then 0 else Polynomial.C (c a) * Polynomial.X ^ (k a - 1)) := by
    change (Polynomial.divX_hom (R := ℤ)) (1 - ∑ a ∈ s, Polynomial.C (c a) * Polynomial.X ^ k a) = _
    simp only [map_sub, map_sum, Polynomial.divX_hom_toFun, Polynomial.divX_one,
      Polynomial.divX_C_mul_X_pow, zero_sub]
  rw [hd,Polynomial.eval₂_neg,Polynomial.eval₂_finsetSum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : k a = 0
  · simp [ha]
  · simp only [ha,if_false,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    simp only [Polynomial.eval₂_C,map_neg]
    have hc : (Int.castRingHom (MvPolynomial (Fin 3) ℤ)) (c a) = MvPolynomial.C (c a) :=
      (map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 3) ℤ) (c a)).symm
    rw [hc,neg_mul]
end BurghartPolynomial
namespace BurghartCertificate
open SimpleGraph Finset
theorem fringe_expanded (G : SimpleGraph (Fin 28)) (v : Fin 28) :
    (Burghart.MPolynomial.fringeP G 0 v).divX.eval₂ (Int.castRingHom (MvPolynomial (Fin 3) ℤ)) (MvPolynomial.X (2:Fin 3)) =
      ∑ A ∈ (Burghart.MPolynomial.fringeLeaves G 0 v).powerset,
        if (Burghart.MPolynomial.leafPathUnion G v A).card = 0 then (0 : MvPolynomial (Fin 3) ℤ)
        else MvPolynomial.C (-((-1:ℤ)^A.card)) *
          MvPolynomial.X (2:Fin 3) ^ ((Burghart.MPolynomial.leafPathUnion G v A).card - 1) := by
  classical
  unfold Burghart.MPolynomial.fringeP
  exact BurghartPolynomial.quotient_expansion
    (Burghart.MPolynomial.fringeLeaves G 0 v).powerset (fun A => (-1:ℤ)^A.card)
    (fun A => (Burghart.MPolynomial.leafPathUnion G v A).card)

#print axioms fringe_expanded

set_option maxHeartbeats 20000 in
open scoped Classical in
theorem m_eq_rep (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (r : Fin 28 → Fin 28 → List (Fin 28)) (hr : RoutesOK G r) (ht : G.IsTree)
    (C : Finset (Finset (Fin 28)))
    (hC : univ.powerset.filter (Burghart.MPolynomial.IsAdmissible G 0) = C) :
    Burghart.MPolynomial.mPolynomial G 0 =
      BurghartReflection.eval (repOf G (distanceCode r) C) := by
  classical
  trace "m0"
  unfold Burghart.MPolynomial.mPolynomial repOf
  trace "m1"
  rw [hC,BurghartReflection.eval_sum]
  trace "m2"
  apply Finset.sum_congr rfl
  intro S _
  trace "m3"
  change MvPolynomial.X (0:Fin 3)^S.card *
    MvPolynomial.X (1:Fin 3)^((boundaryCode G S).card - 1) *
      (∑ v ∈ boundaryCode G S, _) = _
  trace "m4"
  rw [Finset.mul_sum,BurghartReflection.eval_sum]
  trace "m5"
  apply Finset.sum_congr rfl
  intro v _
  rw [fringe_expanded,fringe_eq_code G r hr ht v,Finset.mul_sum,BurghartReflection.eval_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [paths_eq_code G r hr ht v A]
  by_cases hA : (pathsCode (distanceCode r) v A).card = 0
  · simp [hA,BurghartReflection.eval_zero]
  · simp only [hA,if_false,BurghartReflection.eval_single]
    ring


#print axioms fringe_expanded
#print axioms m_eq_rep
end BurghartCertificate
