/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGlobalAssembly

/-!
# Exact statement bridge for the RG submission

The energy definition and the two target conclusions below follow PR #7399,
statement commit 3654bf2bddc5217f904b7b85207b1091e833de49, file
FormalConjectures/Paper/RadenkovicGutmanLaplacianEnergy.lean.
This module proves equivalence of statements. Its two implication lemmas
retain their explicit global-conclusion premise.
-/
namespace Gebendorfer.RadenkovicGutman.SubmissionStatement
open SimpleGraph
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency true

/-- The exact actual-mean-degree energy used by the submission. -/
noncomputable def laplacianEnergy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ v : V, |(G.isHermitian_lapMatrix ℝ).eigenvalues v -
    2 * (G.edgeFinset.card : ℝ) / Fintype.card V|

theorem energy_agrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    laplacianEnergy G = Gebendorfer.RadenkovicGutman.laplacianEnergy G := by
  rfl

attribute [local irreducible] laplacianEnergy Gebendorfer.RadenkovicGutman.laplacianEnergy

theorem energy_agrees_of_decidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : DecidableRel G.Adj) :
    @Gebendorfer.RadenkovicGutman.laplacianEnergy V _ _ G d = laplacianEnergy G := by
  exact (GlobalAssembly.energy_decidable_irrel G d _).trans (energy_agrees G).symm

theorem conclusion_agrees (n : ℕ) (T : SimpleGraph (Fin n)) :
    GlobalAssembly.Conclusion T ↔
      (laplacianEnergy (pathGraph n) ≤ laplacianEnergy T ∧
        (laplacianEnergy T = laplacianEnergy (pathGraph n) ↔
          Nonempty (T ≃g pathGraph n))) := by
  simp only [GlobalAssembly.Conclusion,energy_agrees_of_decidable]

theorem path_minimum_of_conclusion (n : ℕ) (T : SimpleGraph (Fin n))
    (h : GlobalAssembly.Conclusion T) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy T :=
  ((conclusion_agrees n T).mp h).1

theorem path_equality_of_conclusion (n : ℕ) (T : SimpleGraph (Fin n))
    (h : GlobalAssembly.Conclusion T) :
    laplacianEnergy T = laplacianEnergy (pathGraph n) ↔
      Nonempty (T ≃g pathGraph n) :=
  ((conclusion_agrees n T).mp h).2

#print axioms energy_agrees
#print axioms energy_agrees_of_decidable
#print axioms conclusion_agrees
#print axioms path_minimum_of_conclusion
#print axioms path_equality_of_conclusion
end
end Gebendorfer.RadenkovicGutman.SubmissionStatement
