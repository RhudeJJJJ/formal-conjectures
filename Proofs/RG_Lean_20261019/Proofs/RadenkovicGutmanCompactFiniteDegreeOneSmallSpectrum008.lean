/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum008
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,false,true,false,false],![true,false,true,true,false,false,false],![false,true,false,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,false,true,false],![false,false,false,false,true,false,true],![false,false,false,false,false,true,false]]
noncomputable def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,7,-52,116,-114,54,-12,1]
noncomputable def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0;0,(-3/11),1,0,0,0,0;0,(-3/11),(-3/19),1,0,0,0;(-1/3),(-1/11),(-1/19),(-1/16),1,0,0;0,0,0,0,(-8/21),1,0;0,0,0,0,0,(-21/55),1],!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/19),1,0,0,0,0;0,(-4/19),(-4/53),1,0,0,0;(-1/4),(-1/19),(-1/53),(-1/49),1,0,0;0,0,0,0,(-49/183),1,0;0,0,0,0,0,(-183/683),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/29),1,0,0,0,0;0,(-5/29),(-5/111),1,0,0,0;(-1/5),(-1/29),(-1/111),(-1/106),1,0,0;0,0,0,0,(-53/254),1,0;0,0,0,0,0,(-254/1217),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/41),1,0,0,0,0;0,(-6/41),(-6/199),1,0,0,0;(-1/6),(-1/41),(-1/199),(-1/193),1,0,0;0,0,0,0,(-193/1125),1,0;0,0,0,0,0,(-1125/6557),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/55),1,0,0,0,0;0,(-7/55),(-7/323),1,0,0,0;(-1/7),(-1/55),(-1/323),(-1/316),1,0,0;0,0,0,0,(-158/1083),1,0;0,0,0,0,0,(-1083/7423),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/71),1,0,0,0,0;0,(-8/71),(-8/489),1,0,0,0;(-1/8),(-1/71),(-1/489),(-1/481),1,0,0;0,0,0,0,(-481/3787),1,0;0,0,0,0,0,(-3787/29815),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/89),1,0,0,0,0;0,(-9/89),(-9/703),1,0,0,0;(-1/9),(-1/89),(-1/703),(-1/694),1,0,0;0,0,0,0,(-347/3084),1,0;0,0,0,0,0,(-3084/27409),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/109),1,0,0,0,0;0,(-10/109),(-10/971),1,0,0,0;(-1/10),(-1/109),(-1/971),(-1/961),1,0,0;0,0,0,0,(-961/9513),1,0;0,0,0,0,0,(-9513/94169),1]]
noncomputable def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-3,1,0,0,1,0,0;0,(-11/3),1,1,(1/3),0,0;0,0,(-19/11),(3/11),(1/11),0,0;0,0,0,(-32/19),(2/19),0,0;0,0,0,0,(-21/8),1,0;0,0,0,0,0,(-55/21),1;0,0,0,0,0,0,(-89/55)],!![-4,1,0,0,1,0,0;0,(-19/4),1,1,(1/4),0,0;0,0,(-53/19),(4/19),(1/19),0,0;0,0,0,(-147/53),(3/53),0,0;0,0,0,0,(-183/49),1,0;0,0,0,0,0,(-683/183),1;0,0,0,0,0,0,(-1866/683)],!![-5,1,0,0,1,0,0;0,(-29/5),1,1,(1/5),0,0;0,0,(-111/29),(5/29),(1/29),0,0;0,0,0,(-424/111),(4/111),0,0;0,0,0,0,(-254/53),1,0;0,0,0,0,0,(-1217/254),1;0,0,0,0,0,0,(-4614/1217)],!![-6,1,0,0,1,0,0;0,(-41/6),1,1,(1/6),0,0;0,0,(-199/41),(6/41),(1/41),0,0;0,0,0,(-965/199),(5/199),0,0;0,0,0,0,(-1125/193),1,0;0,0,0,0,0,(-6557/1125),1;0,0,0,0,0,0,(-31660/6557)],!![-7,1,0,0,1,0,0;0,(-55/7),1,1,(1/7),0,0;0,0,(-323/55),(7/55),(1/55),0,0;0,0,0,(-1896/323),(6/323),0,0;0,0,0,0,(-1083/158),1,0;0,0,0,0,0,(-7423/1083),1;0,0,0,0,0,0,(-43455/7423)],!![-8,1,0,0,1,0,0;0,(-71/8),1,1,(1/8),0,0;0,0,(-489/71),(8/71),(1/71),0,0;0,0,0,(-3367/489),(7/489),0,0;0,0,0,0,(-3787/481),1,0;0,0,0,0,0,(-29815/3787),1;0,0,0,0,0,0,(-204918/29815)],!![-9,1,0,0,1,0,0;0,(-89/9),1,1,(1/9),0,0;0,0,(-703/89),(9/89),(1/89),0,0;0,0,0,(-5552/703),(8/703),0,0;0,0,0,0,(-3084/347),1,0;0,0,0,0,0,(-27409/3084),1;0,0,0,0,0,0,(-216188/27409)],!![-10,1,0,0,1,0,0;0,(-109/10),1,1,(1/10),0,0;0,0,(-971/109),(10/109),(1/109),0,0;0,0,0,(-8649/971),(9/971),0,0;0,0,0,0,(-9513/961),1,0;0,0,0,0,0,(-94169/9513),1;0,0,0,0,0,0,(-838008/94169)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-38,33,-10,1],count := 5,lower := ![(-1/268435456),(60499199/268435456),(586769129/268435456),(225513251/67108864),(1135033199/268435456)],upper := ![(7/134217728),(30249607/134217728),(73346143/33554432),(902053019/268435456),(567516607/134217728)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((2175827727/469762048) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((8703311223/1879048192) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/7)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum008
