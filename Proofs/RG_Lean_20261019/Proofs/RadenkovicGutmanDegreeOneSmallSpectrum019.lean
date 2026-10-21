/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum019
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,true,false,false,false],![true,false,true,true,false,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,false,true,false,false],![false,false,false,false,true,false,true,true],![false,false,false,false,false,true,false,false],![false,false,false,false,false,true,false,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,74,-214,289,-204,76,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/11),1,0,0,0,0,0;0,(-3/11),(-3/19),1,0,0,0,0;(-1/3),(-1/11),(-1/19),(-1/16),1,0,0,0;0,0,0,0,(-8/21),1,0,0;0,0,0,0,0,(-21/76),1,0;0,0,0,0,0,(-21/76),(-21/131),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/19),1,0,0,0,0,0;0,(-4/19),(-4/53),1,0,0,0,0;(-1/4),(-1/19),(-1/53),(-1/49),1,0,0,0;0,0,0,0,(-49/183),1,0,0;0,0,0,0,0,(-183/866),1,0;0,0,0,0,0,(-183/866),(-61/805),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/29),1,0,0,0,0,0;0,(-5/29),(-5/111),1,0,0,0,0;(-1/5),(-1/29),(-1/111),(-1/106),1,0,0,0;0,0,0,0,(-53/254),1,0,0;0,0,0,0,0,(-254/1471),1,0;0,0,0,0,0,(-254/1471),(-127/2815),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/41),1,0,0,0,0,0;0,(-6/41),(-6/199),1,0,0,0,0;(-1/6),(-1/41),(-1/199),(-1/193),1,0,0,0;0,0,0,0,(-193/1125),1,0,0;0,0,0,0,0,(-1125/7682),1,0;0,0,0,0,0,(-1125/7682),(-225/7457),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/55),1,0,0,0,0,0;0,(-7/55),(-7/323),1,0,0,0,0;(-1/7),(-1/55),(-1/323),(-1/316),1,0,0,0;0,0,0,0,(-158/1083),1,0,0;0,0,0,0,0,(-1083/8506),1,0;0,0,0,0,0,(-1083/8506),(-361/16651),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/71),1,0,0,0,0,0;0,(-8/71),(-8/489),1,0,0,0,0;(-1/8),(-1/71),(-1/489),(-1/481),1,0,0,0;0,0,0,0,(-481/3787),1,0,0;0,0,0,0,0,(-3787/33602),1,0;0,0,0,0,0,(-3787/33602),(-541/33061),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/89),1,0,0,0,0,0;0,(-9/89),(-9/703),1,0,0,0,0;(-1/9),(-1/89),(-1/703),(-1/694),1,0,0,0;0,0,0,0,(-347/3084),1,0,0;0,0,0,0,0,(-3084/30493),1,0;0,0,0,0,0,(-3084/30493),(-771/60215),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/109),1,0,0,0,0,0;0,(-10/109),(-10/971),1,0,0,0,0;(-1/10),(-1/109),(-1/971),(-1/961),1,0,0,0;0,0,0,0,(-961/9513),1,0,0;0,0,0,0,0,(-9513/103682),1,0;0,0,0,0,0,(-9513/103682),(-1057/102625),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/131),1,0,0,0,0,0;0,(-11/131),(-11/1299),1,0,0,0,0;(-1/11),(-1/131),(-1/1299),(-1/1288),1,0,0,0;0,0,0,0,(-644/7025),1,0,0;0,0,0,0,0,(-7025/83656),1,0;0,0,0,0,0,(-7025/83656),(-1405/165907),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,1,0,0,0;0,(-11/3),1,1,(1/3),0,0,0;0,0,(-19/11),(3/11),(1/11),0,0,0;0,0,0,(-32/19),(2/19),0,0,0;0,0,0,0,(-21/8),1,0,0;0,0,0,0,0,(-76/21),1,1;0,0,0,0,0,0,(-131/76),(21/76);0,0,0,0,0,0,0,(-220/131)],!![-4,1,0,0,1,0,0,0;0,(-19/4),1,1,(1/4),0,0,0;0,0,(-53/19),(4/19),(1/19),0,0,0;0,0,0,(-147/53),(3/53),0,0,0;0,0,0,0,(-183/49),1,0,0;0,0,0,0,0,(-866/183),1,1;0,0,0,0,0,0,(-2415/866),(183/866);0,0,0,0,0,0,0,(-2232/805)],!![-5,1,0,0,1,0,0,0;0,(-29/5),1,1,(1/5),0,0,0;0,0,(-111/29),(5/29),(1/29),0,0,0;0,0,0,(-424/111),(4/111),0,0,0;0,0,0,0,(-254/53),1,0,0;0,0,0,0,0,(-1471/254),1,1;0,0,0,0,0,0,(-5630/1471),(254/1471);0,0,0,0,0,0,0,(-10752/2815)],!![-6,1,0,0,1,0,0,0;0,(-41/6),1,1,(1/6),0,0,0;0,0,(-199/41),(6/41),(1/41),0,0,0;0,0,0,(-965/199),(5/199),0,0,0;0,0,0,0,(-1125/193),1,0,0;0,0,0,0,0,(-7682/1125),1,1;0,0,0,0,0,0,(-37285/7682),(1125/7682);0,0,0,0,0,0,0,(-36160/7457)],!![-7,1,0,0,1,0,0,0;0,(-55/7),1,1,(1/7),0,0,0;0,0,(-323/55),(7/55),(1/55),0,0,0;0,0,0,(-1896/323),(6/323),0,0,0;0,0,0,0,(-1083/158),1,0,0;0,0,0,0,0,(-8506/1083),1,1;0,0,0,0,0,0,(-49953/8506),(1083/8506);0,0,0,0,0,0,0,(-97740/16651)],!![-8,1,0,0,1,0,0,0;0,(-71/8),1,1,(1/8),0,0,0;0,0,(-489/71),(8/71),(1/71),0,0,0;0,0,0,(-3367/489),(7/489),0,0,0;0,0,0,0,(-3787/481),1,0,0;0,0,0,0,0,(-33602/3787),1,1;0,0,0,0,0,0,(-231427/33602),(3787/33602);0,0,0,0,0,0,0,(-32520/4723)],!![-9,1,0,0,1,0,0,0;0,(-89/9),1,1,(1/9),0,0,0;0,0,(-703/89),(9/89),(1/89),0,0,0;0,0,0,(-5552/703),(8/703),0,0,0;0,0,0,0,(-3084/347),1,0,0;0,0,0,0,0,(-30493/3084),1,1;0,0,0,0,0,0,(-240860/30493),(3084/30493);0,0,0,0,0,0,0,(-475552/60215)],!![-10,1,0,0,1,0,0,0;0,(-109/10),1,1,(1/10),0,0,0;0,0,(-971/109),(10/109),(1/109),0,0,0;0,0,0,(-8649/971),(9/971),0,0,0;0,0,0,0,(-9513/961),1,0,0;0,0,0,0,0,(-103682/9513),1,1;0,0,0,0,0,0,(-923625/103682),(9513/103682);0,0,0,0,0,0,0,(-914112/102625)],!![-11,1,0,0,1,0,0,0;0,(-131/11),1,1,(1/11),0,0,0;0,0,(-1299/131),(11/131),(1/131),0,0,0;0,0,0,(-12880/1299),(10/1299),0,0,0;0,0,0,0,(-7025/644),1,0,0;0,0,0,0,0,(-83656/7025),1,1;0,0,0,0,0,0,(-829535/83656),(7025/83656);0,0,0,0,0,0,0,(-1645020/165907)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,8,-50,40,-11,1],count := 5,lower := ![(-15/536870912),(25017311/134217728),(663219029/268435456),(2147483641/536870912),(582897267/134217728)],upper := ![(1/268435456),(100069261/536870912),(1326438075/536870912),(1073741829/268435456),(2331589085/536870912)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(536870899/536870912)],upper := ![(134217729/134217728)],copies := 3}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((2986938479/536870912) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((1493469265/268435456) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/8)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum019
