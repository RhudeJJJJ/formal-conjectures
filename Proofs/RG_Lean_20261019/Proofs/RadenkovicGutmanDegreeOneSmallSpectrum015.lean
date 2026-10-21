/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum015
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,true,false,true,false],![true,false,true,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,true,false,false],![false,false,false,true,false,false,false],![true,false,false,false,false,false,true],![false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-48,114,-114,54,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/11),1,0,0,0,0;(-1/4),(-1/11),(-1/18),1,0,0,0;0,0,0,(-18/49),1,0,0;(-1/4),(-1/11),(-1/18),(-5/49),(-1/16),1,0;0,0,0,0,0,(-16/43),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/19),1,0,0,0,0;(-1/5),(-1/19),(-1/52),1,0,0,0;0,0,0,(-52/197),1,0,0;(-1/5),(-1/19),(-1/52),(-11/197),(-1/49),1,0;0,0,0,0,0,(-49/185),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/29),1,0,0,0,0;(-1/6),(-1/29),(-1/110),1,0,0,0;0,0,0,(-110/531),1,0,0;(-1/6),(-1/29),(-1/110),(-19/531),(-1/106),1,0;0,0,0,0,0,(-106/511),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/41),1,0,0,0,0;(-1/7),(-1/41),(-1/198),1,0,0,0;0,0,0,(-198/1159),1,0,0;(-1/7),(-1/41),(-1/198),(-29/1159),(-1/193),1,0;0,0,0,0,0,(-193/1129),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/55),1,0,0,0,0;(-1/8),(-1/55),(-1/322),1,0,0,0;0,0,0,(-322/2213),1,0,0;(-1/8),(-1/55),(-1/322),(-41/2213),(-1/316),1,0;0,0,0,0,0,(-316/2171),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/71),1,0,0,0,0;(-1/9),(-1/71),(-1/488),1,0,0,0;0,0,0,(-488/3849),1,0,0;(-1/9),(-1/71),(-1/488),(-55/3849),(-1/481),1,0;0,0,0,0,0,(-481/3793),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/89),1,0,0,0,0;(-1/10),(-1/89),(-1/702),1,0,0,0;0,0,0,(-702/6247),1,0,0;(-1/10),(-1/89),(-1/702),(-71/6247),(-1/694),1,0;0,0,0,0,0,(-694/6175),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;0,(-11/109),1,0,0,0,0;(-1/11),(-1/109),(-1/970),1,0,0,0;0,0,0,(-970/9611),1,0,0;(-1/11),(-1/109),(-1/970),(-89/9611),(-1/961),1,0;0,0,0,0,0,(-961/9521),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-4,1,0,1,0,1,0;0,(-11/4),1,(1/4),0,(1/4),0;0,0,(-18/11),(1/11),0,(1/11),0;0,0,0,(-49/18),1,(5/18),0;0,0,0,0,(-80/49),(5/49),0;0,0,0,0,0,(-43/16),1;0,0,0,0,0,0,(-70/43)],!![-5,1,0,1,0,1,0;0,(-19/5),1,(1/5),0,(1/5),0;0,0,(-52/19),(1/19),0,(1/19),0;0,0,0,(-197/52),1,(11/52),0;0,0,0,0,(-539/197),(11/197),0;0,0,0,0,0,(-185/49),1;0,0,0,0,0,0,(-506/185)],!![-6,1,0,1,0,1,0;0,(-29/6),1,(1/6),0,(1/6),0;0,0,(-110/29),(1/29),0,(1/29),0;0,0,0,(-531/110),1,(19/110),0;0,0,0,0,(-2014/531),(19/531),0;0,0,0,0,0,(-511/106),1;0,0,0,0,0,0,(-1938/511)],!![-7,1,0,1,0,1,0;0,(-41/7),1,(1/7),0,(1/7),0;0,0,(-198/41),(1/41),0,(1/41),0;0,0,0,(-1159/198),1,(29/198),0;0,0,0,0,(-5597/1159),(29/1159),0;0,0,0,0,0,(-1129/193),1;0,0,0,0,0,0,(-5452/1129)],!![-8,1,0,1,0,1,0;0,(-55/8),1,(1/8),0,(1/8),0;0,0,(-322/55),(1/55),0,(1/55),0;0,0,0,(-2213/322),1,(41/322),0;0,0,0,0,(-12956/2213),(41/2213),0;0,0,0,0,0,(-2171/316),1;0,0,0,0,0,0,(-12710/2171)],!![-9,1,0,1,0,1,0;0,(-71/9),1,(1/9),0,(1/9),0;0,0,(-488/71),(1/71),0,(1/71),0;0,0,0,(-3849/488),1,(55/488),0;0,0,0,0,(-26455/3849),(55/3849),0;0,0,0,0,0,(-3793/481),1;0,0,0,0,0,0,(-26070/3793)],!![-10,1,0,1,0,1,0;0,(-89/10),1,(1/10),0,(1/10),0;0,0,(-702/89),(1/89),0,(1/89),0;0,0,0,(-6247/702),1,(71/702),0;0,0,0,0,(-49274/6247),(71/6247),0;0,0,0,0,0,(-6175/694),1;0,0,0,0,0,0,(-48706/6175)],!![-11,1,0,1,0,1,0;0,(-109/11),1,(1/11),0,(1/11),0;0,0,(-970/109),(1/109),0,(1/109),0;0,0,0,(-9611/970),1,(89/970),0;0,0,0,0,(-85529/9611),(89/9611),0;0,0,0,0,0,(-9521/961),1;0,0,0,0,0,0,(-84728/9521)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-6,1],count := 3,lower := ![(-1/268435456),(212840647/134217728),(1184931419/268435456)],upper := ![(7/134217728),(425681309/268435456),(592465717/134217728)],copies := 1},{coefficients := [1,-3,1],count := 2,lower := ![(102533219/268435456),(87846643/33554432)],upper := ![(51266617/134217728),(702773159/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((8469667533/1879048192) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((1058708481/234881024) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum015
