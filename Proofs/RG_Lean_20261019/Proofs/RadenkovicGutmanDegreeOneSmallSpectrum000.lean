/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum000
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 4 → Fin 4 → Bool := ![![false,true,true,false],![true,false,false,false],![true,false,false,true],![false,false,true,false]]
def graph : SimpleGraph (Fin 4) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-4,10,-6,1]
def lowerMatrices : Fin 5 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;(-1/3),1,0,0;(-1/3),(-1/5),1,0;0,0,(-5/13),1],!![1,0,0,0;(-1/4),1,0,0;(-1/4),(-1/11),1,0;0,0,(-11/41),1],!![1,0,0,0;(-1/5),1,0,0;(-1/5),(-1/19),1,0;0,0,(-19/91),1],!![1,0,0,0;(-1/6),1,0,0;(-1/6),(-1/29),1,0;0,0,(-29/169),1],!![1,0,0,0;(-1/7),1,0,0;(-1/7),(-1/41),1,0;0,0,(-41/281),1]]
def upperMatrices : Fin 5 → Matrix (Fin 4) (Fin 4) ℚ := ![!![-3,1,1,0;0,(-5/3),(1/3),0;0,0,(-13/5),1;0,0,0,(-21/13)],!![-4,1,1,0;0,(-11/4),(1/4),0;0,0,(-41/11),1;0,0,0,(-112/41)],!![-5,1,1,0;0,(-19/5),(1/5),0;0,0,(-91/19),1;0,0,0,(-345/91)],!![-6,1,1,0;0,(-29/6),(1/6),0;0,0,(-169/29),1;0,0,0,(-816/169)],!![-7,1,1,0;0,(-41/7),(1/7),0;0,0,(-281/41),1;0,0,0,(-1645/281)]]
theorem matrix_certificates : ∀ k : Fin 5,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-4,10,-6,1],count := 4,lower := ![(-7/268435456),(78622921/134217728),(536870909/268435456),(916495967/268435456)],upper := ![(1/134217728),(157245851/268435456),(268435459/134217728),(114561997/33554432)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((162015127/67108864) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/4) ∧
    stopLoss (laplacianSpectrum graph) (2-2/4) ≤ ((324030263/134217728) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/4)
  norm_num [boxes,FactoredRoots.lowerTotal,FactoredRoots.upperTotal,FactoredRoots.lower,
    FactoredRoots.upper,Fin.sum_univ_succ] at h ⊢
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum000
