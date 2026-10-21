/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum005
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 6 → Fin 6 → Bool := ![![false,true,true,true,false,false],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,true,true],![false,false,false,true,false,false],![false,false,false,true,false,false]]
def graph : SimpleGraph (Fin 6) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-6,29,-48,34,-10,1]
def lowerMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;(-1/4),1,0,0,0,0;(-1/4),(-1/7),1,0,0,0;(-1/4),(-1/7),(-1/6),1,0,0;0,0,0,(-3/11),1,0;0,0,0,(-3/11),(-3/19),1],!![1,0,0,0,0,0;(-1/5),1,0,0,0,0;(-1/5),(-1/14),1,0,0,0;(-1/5),(-1/14),(-1/13),1,0,0;0,0,0,(-13/62),1,0;0,0,0,(-13/62),(-13/173),1],!![1,0,0,0,0,0;(-1/6),1,0,0,0,0;(-1/6),(-1/23),1,0,0,0;(-1/6),(-1/23),(-1/22),1,0,0;0,0,0,(-11/64),1,0;0,0,0,(-11/64),(-11/245),1],!![1,0,0,0,0,0;(-1/7),1,0,0,0,0;(-1/7),(-1/34),1,0,0,0;(-1/7),(-1/34),(-1/33),1,0,0;0,0,0,(-33/226),1,0;0,0,0,(-33/226),(-33/1097),1],!![1,0,0,0,0,0;(-1/8),1,0,0,0,0;(-1/8),(-1/47),1,0,0,0;(-1/8),(-1/47),(-1/46),1,0,0;0,0,0,(-23/181),1,0;0,0,0,(-23/181),(-23/1063),1],!![1,0,0,0,0,0;(-1/9),1,0,0,0,0;(-1/9),(-1/62),1,0,0,0;(-1/9),(-1/62),(-1/61),1,0,0;0,0,0,(-61/542),1,0;0,0,0,(-61/542),(-61/3733),1],!![1,0,0,0,0,0;(-1/10),1,0,0,0,0;(-1/10),(-1/79),1,0,0,0;(-1/10),(-1/79),(-1/78),1,0,0;0,0,0,(-39/386),1,0;0,0,0,(-39/386),(-39/3049),1]]
def upperMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![-4,1,1,1,0,0;0,(-7/4),(1/4),(1/4),0,0;0,0,(-12/7),(2/7),0,0;0,0,0,(-11/3),1,1;0,0,0,0,(-19/11),(3/11);0,0,0,0,0,(-32/19)],!![-5,1,1,1,0,0;0,(-14/5),(1/5),(1/5),0,0;0,0,(-39/14),(3/14),0,0;0,0,0,(-62/13),1,1;0,0,0,0,(-173/62),(13/62);0,0,0,0,0,(-480/173)],!![-6,1,1,1,0,0;0,(-23/6),(1/6),(1/6),0,0;0,0,(-88/23),(4/23),0,0;0,0,0,(-64/11),1,1;0,0,0,0,(-245/64),(11/64);0,0,0,0,0,(-936/245)],!![-7,1,1,1,0,0;0,(-34/7),(1/7),(1/7),0,0;0,0,(-165/34),(5/34),0,0;0,0,0,(-226/33),1,1;0,0,0,0,(-1097/226),(33/226);0,0,0,0,0,(-5320/1097)],!![-8,1,1,1,0,0;0,(-47/8),(1/8),(1/8),0,0;0,0,(-276/47),(6/47),0,0;0,0,0,(-181/23),1,1;0,0,0,0,(-1063/181),(23/181);0,0,0,0,0,(-6240/1063)],!![-9,1,1,1,0,0;0,(-62/9),(1/9),(1/9),0,0;0,0,(-427/62),(7/62),0,0;0,0,0,(-542/61),1,1;0,0,0,0,(-3733/542),(61/542);0,0,0,0,0,(-25704/3733)],!![-10,1,1,1,0,0;0,(-79/10),(1/10),(1/10),0,0;0,0,(-624/79),(8/79),0,0;0,0,0,(-386/39),1,1;0,0,0,0,(-3049/386),(39/386);0,0,0,0,0,(-24080/3049)]]
theorem matrix_certificates : ∀ k : Fin 7,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-6,17,-8,1],count := 4,lower := ![(-3/268435456),(117694769/268435456),(201326589/67108864),(1224482503/268435456)],upper := ![(5/134217728),(58847391/134217728),(805306369/268435456),(306120629/67108864)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217725/134217728)],upper := ![(268435463/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((3405012017/805306368) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/6) ∧
    stopLoss (laplacianSpectrum graph) (2-2/6) ≤ ((3405012095/805306368) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/6)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum005
