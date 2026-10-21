/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum002
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 5 → Fin 5 → Bool := ![![false,true,true,true,false],![true,false,false,false,false],![true,false,false,false,false],![true,false,false,false,true],![false,false,false,true,false]]
def graph : SimpleGraph (Fin 5) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,5,-18,20,-8,1]
def lowerMatrices : Fin 6 → Matrix (Fin 5) (Fin 5) ℚ := ![!![1,0,0,0,0;(-1/4),1,0,0,0;(-1/4),(-1/7),1,0,0;(-1/4),(-1/7),(-1/6),1,0;0,0,0,(-3/8),1],!![1,0,0,0,0;(-1/5),1,0,0,0;(-1/5),(-1/14),1,0,0;(-1/5),(-1/14),(-1/13),1,0;0,0,0,(-13/49),1],!![1,0,0,0,0;(-1/6),1,0,0,0;(-1/6),(-1/23),1,0,0;(-1/6),(-1/23),(-1/22),1,0;0,0,0,(-11/53),1],!![1,0,0,0,0;(-1/7),1,0,0,0;(-1/7),(-1/34),1,0,0;(-1/7),(-1/34),(-1/33),1,0;0,0,0,(-33/193),1],!![1,0,0,0,0;(-1/8),1,0,0,0;(-1/8),(-1/47),1,0,0;(-1/8),(-1/47),(-1/46),1,0;0,0,0,(-23/158),1],!![1,0,0,0,0;(-1/9),1,0,0,0;(-1/9),(-1/62),1,0,0;(-1/9),(-1/62),(-1/61),1,0;0,0,0,(-61/481),1]]
def upperMatrices : Fin 6 → Matrix (Fin 5) (Fin 5) ℚ := ![!![-4,1,1,1,0;0,(-7/4),(1/4),(1/4),0;0,0,(-12/7),(2/7),0;0,0,0,(-8/3),1;0,0,0,0,(-13/8)],!![-5,1,1,1,0;0,(-14/5),(1/5),(1/5),0;0,0,(-39/14),(3/14),0;0,0,0,(-49/13),1;0,0,0,0,(-134/49)],!![-6,1,1,1,0;0,(-23/6),(1/6),(1/6),0;0,0,(-88/23),(4/23),0;0,0,0,(-53/11),1;0,0,0,0,(-201/53)],!![-7,1,1,1,0;0,(-34/7),(1/7),(1/7),0;0,0,(-165/34),(5/34),0;0,0,0,(-193/33),1;0,0,0,0,(-932/193)],!![-8,1,1,1,0;0,(-47/8),(1/8),(1/8),0;0,0,(-276/47),(6/47),0;0,0,0,(-158/23),1;0,0,0,0,(-925/158)],!![-9,1,1,1,0;0,(-62/9),(1/9),(1/9),0;0,0,(-427/62),(7/62),0;0,0,0,(-481/61),1;0,0,0,0,(-3306/481)]]
theorem matrix_certificates : ∀ k : Fin 6,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,5,-18,20,-8,1],count := 5,lower := ![(-3/268435456),(69632919/134217728),(134217725/134217728),(620383277/268435456),(559699529/134217728)],upper := ![(1/33554432),(139265849/268435456),(268435461/268435456),(77547911/33554432),(1119399069/268435456)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((4403944379/1342177280) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/5) ∧
    stopLoss (laplacianSpectrum graph) (2-2/5) ≤ ((4403944489/1342177280) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/5)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum002
