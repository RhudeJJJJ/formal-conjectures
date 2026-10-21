/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum001
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 4 → Fin 4 → Bool := ![![false,true,true,true],![true,false,false,false],![true,false,false,false],![true,false,false,false]]
def graph : SimpleGraph (Fin 4) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-4,9,-6,1]
def lowerMatrices : Fin 5 → Matrix (Fin 4) (Fin 4) ℚ := ![!![1,0,0,0;(-1/4),1,0,0;(-1/4),(-1/7),1,0;(-1/4),(-1/7),(-1/6),1],!![1,0,0,0;(-1/5),1,0,0;(-1/5),(-1/14),1,0;(-1/5),(-1/14),(-1/13),1],!![1,0,0,0;(-1/6),1,0,0;(-1/6),(-1/23),1,0;(-1/6),(-1/23),(-1/22),1],!![1,0,0,0;(-1/7),1,0,0;(-1/7),(-1/34),1,0;(-1/7),(-1/34),(-1/33),1],!![1,0,0,0;(-1/8),1,0,0;(-1/8),(-1/47),1,0;(-1/8),(-1/47),(-1/46),1]]
def upperMatrices : Fin 5 → Matrix (Fin 4) (Fin 4) ℚ := ![!![-4,1,1,1;0,(-7/4),(1/4),(1/4);0,0,(-12/7),(2/7);0,0,0,(-5/3)],!![-5,1,1,1;0,(-14/5),(1/5),(1/5);0,0,(-39/14),(3/14);0,0,0,(-36/13)],!![-6,1,1,1;0,(-23/6),(1/6),(1/6);0,0,(-88/23),(4/23);0,0,0,(-42/11)],!![-7,1,1,1;0,(-34/7),(1/7),(1/7);0,0,(-165/34),(5/34);0,0,0,(-160/33)],!![-8,1,1,1;0,(-47/8),(1/8),(1/8);0,0,(-276/47),(6/47);0,0,0,(-135/23)]]
theorem matrix_certificates : ∀ k : Fin 5,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-4,1],count := 2,lower := ![(-7/268435456),(134217727/33554432)],upper := ![(1/134217728),(1073741825/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(268435451/268435456)],upper := ![(67108865/67108864)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((83886079/33554432) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/4) ∧
    stopLoss (laplacianSpectrum graph) (2-2/4) ≤ ((671088641/268435456) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum001
