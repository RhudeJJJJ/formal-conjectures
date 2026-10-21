/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum025
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,false,true,false,false],![true,false,true,false,true,false,false,false],![false,true,false,true,false,false,false,false],![false,false,true,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,false,false,true,false],![false,false,false,false,false,true,false,true],![false,false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,76,-228,308,-212,77,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/11),1,0,0,0,0,0;0,0,(-11/30),1,0,0,0,0;0,(-3/11),(-1/10),(-3/49),1,0,0,0;(-1/3),(-1/11),(-1/30),(-1/49),(-5/83),1,0,0;0,0,0,0,0,(-83/218),1,0;0,0,0,0,0,0,(-218/571),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/19),1,0,0,0,0,0;0,0,(-19/72),1,0,0,0,0;0,(-4/19),(-1/18),(-4/197),1,0,0,0;(-1/4),(-1/19),(-1/72),(-1/197),(-11/547),1,0,0;0,0,0,0,0,(-547/2043),1,0;0,0,0,0,0,0,(-2043/7625),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/29),1,0,0,0,0,0;0,0,(-29/140),1,0,0,0,0;0,(-5/29),(-1/28),(-5/531),1,0,0,0;(-1/5),(-1/29),(-1/140),(-1/531),(-19/2029),1,0,0;0,0,0,0,0,(-2029/9724),1,0;0,0,0,0,0,0,(-9724/46591),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/41),1,0,0,0,0,0;0,0,(-41/240),1,0,0,0,0;0,(-6/41),(-1/40),(-6/1159),1,0,0,0;(-1/6),(-1/41),(-1/240),(-1/1159),(-29/5621),1,0,0;0,0,0,0,0,(-5621/32765),1,0;0,0,0,0,0,0,(-32765/190969),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/55),1,0,0,0,0,0;0,0,(-55/378),1,0,0,0,0;0,(-7/55),(-1/54),(-7/2213),1,0,0,0;(-1/7),(-1/55),(-1/378),(-1/2213),(-41/12991),1,0,0;0,0,0,0,0,(-12991/89046),1,0;0,0,0,0,0,0,(-89046/610331),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/71),1,0,0,0,0,0;0,0,(-71/560),1,0,0,0,0;0,(-8/71),(-1/70),(-8/3849),1,0,0,0;(-1/8),(-1/71),(-1/560),(-1/3849),(-55/26503),1,0,0;0,0,0,0,0,(-26503/208663),1,0;0,0,0,0,0,0,(-208663/1642801),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/89),1,0,0,0,0,0;0,0,(-89/792),1,0,0,0,0;0,(-9/89),(-1/88),(-9/6247),1,0,0,0;(-1/9),(-1/89),(-1/792),(-1/6247),(-71/49337),1,0,0;0,0,0,0,0,(-49337/438488),1,0;0,0,0,0,0,0,(-438488/3897055),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/109),1,0,0,0,0,0;0,0,(-109/1080),1,0,0,0,0;0,(-10/109),(-1/108),(-10/9611),1,0,0,0;(-1/10),(-1/109),(-1/1080),(-1/9611),(-89/85609),1,0,0;0,0,0,0,0,(-85609/847449),1,0;0,0,0,0,0,0,(-847449/8388881),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/131),1,0,0,0,0,0;0,0,(-131/1430),1,0,0,0,0;0,(-11/131),(-1/130),(-11/14169),1,0,0,0;(-1/11),(-1/131),(-1/1430),(-1/14169),(-109/140491),1,0,0;0,0,0,0,0,(-140491/1532530),1,0;0,0,0,0,0,0,(-1532530/16717339),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,0,1,0,0;0,(-11/3),1,0,1,(1/3),0,0;0,0,(-30/11),1,(3/11),(1/11),0,0;0,0,0,(-49/30),(1/10),(1/30),0,0;0,0,0,0,(-83/49),(5/49),0,0;0,0,0,0,0,(-218/83),1,0;0,0,0,0,0,0,(-571/218),1;0,0,0,0,0,0,0,(-924/571)],!![-4,1,0,0,0,1,0,0;0,(-19/4),1,0,1,(1/4),0,0;0,0,(-72/19),1,(4/19),(1/19),0,0;0,0,0,(-197/72),(1/18),(1/72),0,0;0,0,0,0,(-547/197),(11/197),0,0;0,0,0,0,0,(-2043/547),1,0;0,0,0,0,0,0,(-7625/2043),1;0,0,0,0,0,0,0,(-20832/7625)],!![-5,1,0,0,0,1,0,0;0,(-29/5),1,0,1,(1/5),0,0;0,0,(-140/29),1,(5/29),(1/29),0,0;0,0,0,(-531/140),(1/28),(1/140),0,0;0,0,0,0,(-2029/531),(19/531),0,0;0,0,0,0,0,(-9724/2029),1,0;0,0,0,0,0,0,(-46591/9724),1;0,0,0,0,0,0,0,(-176640/46591)],!![-6,1,0,0,0,1,0,0;0,(-41/6),1,0,1,(1/6),0,0;0,0,(-240/41),1,(6/41),(1/41),0,0;0,0,0,(-1159/240),(1/40),(1/240),0,0;0,0,0,0,(-5621/1159),(29/1159),0,0;0,0,0,0,0,(-32765/5621),1,0;0,0,0,0,0,0,(-190969/32765),1;0,0,0,0,0,0,0,(-922080/190969)],!![-7,1,0,0,0,1,0,0;0,(-55/7),1,0,1,(1/7),0,0;0,0,(-378/55),1,(7/55),(1/55),0,0;0,0,0,(-2213/378),(1/54),(1/378),0,0;0,0,0,0,(-12991/2213),(41/2213),0,0;0,0,0,0,0,(-89046/12991),1,0;0,0,0,0,0,0,(-610331/89046),1;0,0,0,0,0,0,0,(-3572940/610331)],!![-8,1,0,0,0,1,0,0;0,(-71/8),1,0,1,(1/8),0,0;0,0,(-560/71),1,(8/71),(1/71),0,0;0,0,0,(-3849/560),(1/70),(1/560),0,0;0,0,0,0,(-26503/3849),(55/3849),0,0;0,0,0,0,0,(-208663/26503),1,0;0,0,0,0,0,0,(-1642801/208663),1;0,0,0,0,0,0,0,(-11290944/1642801)],!![-9,1,0,0,0,1,0,0;0,(-89/9),1,0,1,(1/9),0,0;0,0,(-792/89),1,(9/89),(1/89),0,0;0,0,0,(-6247/792),(1/88),(1/792),0,0;0,0,0,0,(-49337/6247),(71/6247),0,0;0,0,0,0,0,(-438488/49337),1,0;0,0,0,0,0,0,(-3897055/438488),1;0,0,0,0,0,0,0,(-30737952/3897055)],!![-10,1,0,0,0,1,0,0;0,(-109/10),1,0,1,(1/10),0,0;0,0,(-1080/109),1,(10/109),(1/109),0,0;0,0,0,(-9611/1080),(1/108),(1/1080),0,0;0,0,0,0,(-85609/9611),(89/9611),0,0;0,0,0,0,0,(-847449/85609),1,0;0,0,0,0,0,0,(-8388881/847449),1;0,0,0,0,0,0,0,(-74652480/8388881)],!![-11,1,0,0,0,1,0,0;0,(-131/11),1,0,1,(1/11),0,0;0,0,(-1430/131),1,(11/131),(1/131),0,0;0,0,0,(-14169/1430),(1/130),(1/1430),0,0;0,0,0,0,(-140491/14169),(109/14169),0,0;0,0,0,0,0,(-1532530/140491),1,0;0,0,0,0,0,0,(-16717339/1532530),1;0,0,0,0,0,0,0,(-165640860/16717339)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,76,-228,308,-212,77,-14,1],count := 8,lower := ![(-15/536870912),(25017311/134217728),(314491689/536870912),(536870899/536870912),(1073741813/536870912),(663219029/268435456),(1832991937/536870912),(582897267/134217728)],upper := ![(1/268435456),(100069261/536870912),(157245853/268435456),(134217729/134217728),(536870915/268435456),(1326438075/536870912),(916495977/268435456),(2331589085/536870912)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((701666123/134217728) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((175416535/33554432) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum025
