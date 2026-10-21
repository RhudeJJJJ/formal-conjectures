/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum020
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,true,false,false,false],![true,false,true,true,false,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,false,true,false,true],![false,false,false,false,true,false,true,false],![false,false,false,false,false,true,false,false],![false,false,false,false,true,false,false,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,71,-210,288,-204,76,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/11),1,0,0,0,0,0;0,(-3/11),(-3/19),1,0,0,0,0;(-1/3),(-1/11),(-1/19),(-1/16),1,0,0,0;0,0,0,0,(-8/29),1,0,0;0,0,0,0,0,(-29/79),1,0;0,0,0,0,(-8/29),(-8/79),(-8/129),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/19),1,0,0,0,0,0;0,(-4/19),(-4/53),1,0,0,0,0;(-1/4),(-1/19),(-1/53),(-1/49),1,0,0,0;0,0,0,0,(-49/232),1,0,0;0,0,0,0,0,(-232/879),1,0;0,0,0,0,(-49/232),(-49/879),(-49/2405),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/29),1,0,0,0,0,0;0,(-5/29),(-5/111),1,0,0,0,0;(-1/5),(-1/29),(-1/111),(-1/106),1,0,0,0;0,0,0,0,(-53/307),1,0,0;0,0,0,0,0,(-307/1482),1,0;0,0,0,0,(-53/307),(-53/1482),(-53/5621),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/41),1,0,0,0,0,0;0,(-6/41),(-6/199),1,0,0,0,0;(-1/6),(-1/41),(-1/199),(-1/193),1,0,0,0;0,0,0,0,(-193/1318),1,0,0;0,0,0,0,0,(-1318/7715),1,0;0,0,0,0,(-193/1318),(-193/7715),(-193/37257),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/55),1,0,0,0,0,0;0,(-7/55),(-7/323),1,0,0,0,0;(-1/7),(-1/55),(-1/323),(-1/316),1,0,0,0;0,0,0,0,(-158/1241),1,0,0;0,0,0,0,0,(-1241/8529),1,0;0,0,0,0,(-158/1241),(-158/8529),(-158/49933),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/71),1,0,0,0,0,0;0,(-8/71),(-8/489),1,0,0,0,0;(-1/8),(-1/71),(-1/489),(-1/481),1,0,0,0;0,0,0,0,(-481/4268),1,0,0;0,0,0,0,0,(-4268/33663),1,0;0,0,0,0,(-481/4268),(-481/33663),(-481/231373),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/89),1,0,0,0,0,0;0,(-9/89),(-9/703),1,0,0,0,0;(-1/9),(-1/89),(-1/703),(-1/694),1,0,0,0;0,0,0,0,(-347/3431),1,0,0;0,0,0,0,0,(-3431/30532),1,0;0,0,0,0,(-347/3431),(-347/30532),(-347/240825),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/109),1,0,0,0,0,0;0,(-10/109),(-10/971),1,0,0,0,0;(-1/10),(-1/109),(-1/971),(-1/961),1,0,0,0;0,0,0,0,(-961/10474),1,0,0;0,0,0,0,0,(-10474/103779),1,0;0,0,0,0,(-961/10474),(-961/103779),(-961/923537),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/131),1,0,0,0,0,0;0,(-11/131),(-11/1299),1,0,0,0,0;(-1/11),(-1/131),(-1/1299),(-1/1288),1,0,0,0;0,0,0,0,(-644/7669),1,0,0;0,0,0,0,0,(-7669/83715),1,0;0,0,0,0,(-644/7669),(-644/83715),(-644/829481),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,1,0,0,0;0,(-11/3),1,1,(1/3),0,0,0;0,0,(-19/11),(3/11),(1/11),0,0,0;0,0,0,(-32/19),(2/19),0,0,0;0,0,0,0,(-29/8),1,0,1;0,0,0,0,0,(-79/29),1,(8/29);0,0,0,0,0,0,(-129/79),(8/79);0,0,0,0,0,0,0,(-218/129)],!![-4,1,0,0,1,0,0,0;0,(-19/4),1,1,(1/4),0,0,0;0,0,(-53/19),(4/19),(1/19),0,0,0;0,0,0,(-147/53),(3/53),0,0,0;0,0,0,0,(-232/49),1,0,1;0,0,0,0,0,(-879/232),1,(49/232);0,0,0,0,0,0,(-2405/879),(49/879);0,0,0,0,0,0,0,(-6676/2405)],!![-5,1,0,0,1,0,0,0;0,(-29/5),1,1,(1/5),0,0,0;0,0,(-111/29),(5/29),(1/29),0,0,0;0,0,0,(-424/111),(4/111),0,0,0;0,0,0,0,(-307/53),1,0,1;0,0,0,0,0,(-1482/307),1,(53/307);0,0,0,0,0,0,(-5621/1482),(53/1482);0,0,0,0,0,0,0,(-21477/5621)],!![-6,1,0,0,1,0,0,0;0,(-41/6),1,1,(1/6),0,0,0;0,0,(-199/41),(6/41),(1/41),0,0,0;0,0,0,(-965/199),(5/199),0,0,0;0,0,0,0,(-1318/193),1,0,1;0,0,0,0,0,(-7715/1318),1,(193/1318);0,0,0,0,0,0,(-37257/7715),(193/7715);0,0,0,0,0,0,0,(-180688/37257)],!![-7,1,0,0,1,0,0,0;0,(-55/7),1,1,(1/7),0,0,0;0,0,(-323/55),(7/55),(1/55),0,0,0;0,0,0,(-1896/323),(6/323),0,0,0;0,0,0,0,(-1241/158),1,0,1;0,0,0,0,0,(-8529/1241),1,(158/1241);0,0,0,0,0,0,(-49933/8529),(158/8529);0,0,0,0,0,0,0,(-293120/49933)],!![-8,1,0,0,1,0,0,0;0,(-71/8),1,1,(1/8),0,0,0;0,0,(-489/71),(8/71),(1/71),0,0,0;0,0,0,(-3367/489),(7/489),0,0,0;0,0,0,0,(-4268/481),1,0,1;0,0,0,0,0,(-33663/4268),1,(481/4268);0,0,0,0,0,0,(-231373/33663),(481/33663);0,0,0,0,0,0,0,(-1593156/231373)],!![-9,1,0,0,1,0,0,0;0,(-89/9),1,1,(1/9),0,0,0;0,0,(-703/89),(9/89),(1/89),0,0,0;0,0,0,(-5552/703),(8/703),0,0,0;0,0,0,0,(-3431/347),1,0,1;0,0,0,0,0,(-30532/3431),1,(347/3431);0,0,0,0,0,0,(-240825/30532),(347/30532);0,0,0,0,0,0,0,(-1901963/240825)],!![-10,1,0,0,1,0,0,0;0,(-109/10),1,1,(1/10),0,0,0;0,0,(-971/109),(10/109),(1/109),0,0,0;0,0,0,(-8649/971),(9/971),0,0,0;0,0,0,0,(-10474/961),1,0,1;0,0,0,0,0,(-103779/10474),1,(961/10474);0,0,0,0,0,0,(-923537/103779),(961/103779);0,0,0,0,0,0,0,(-8226304/923537)],!![-11,1,0,0,1,0,0,0;0,(-131/11),1,1,(1/11),0,0,0;0,0,(-1299/131),(11/131),(1/131),0,0,0;0,0,0,(-12880/1299),(10/1299),0,0,0;0,0,0,0,(-7669/644),1,0,1;0,0,0,0,0,(-83715/7669),1,(644/7669);0,0,0,0,0,0,(-829481/83715),(644/83715);0,0,0,0,0,0,0,(-8224614/829481)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,71,-210,288,-204,76,-14,1],count := 8,lower := ![(-15/536870912),(3584993/16777216),(331638535/536870912),(536870899/536870912),(804063673/536870912),(157956397/67108864),(515507091/134217728),(600805067/134217728)],upper := ![(1/268435456),(114719793/536870912),(41454819/67108864),(134217729/134217728),(402031845/268435456),(1263651193/536870912),(2062028381/536870912),(2403220285/536870912)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((90947735/16777216) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((2910327571/536870912) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum020
