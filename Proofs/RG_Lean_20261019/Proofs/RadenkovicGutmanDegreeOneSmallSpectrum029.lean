/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum029
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,false,true,false,false],![true,false,true,true,true,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,false,false,true,true],![false,false,false,false,false,true,false,false],![false,false,false,false,false,true,false,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,66,-188,259,-190,74,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/14),1,0,0,0,0,0;0,(-3/14),(-3/25),1,0,0,0,0;0,(-3/14),(-3/25),(-3/22),1,0,0,0;(-1/3),(-1/14),(-1/25),(-1/22),(-1/19),1,0,0;0,0,0,0,0,(-19/69),1,0;0,0,0,0,0,(-19/69),(-19/119),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/23),1,0,0,0,0,0;0,(-4/23),(-4/65),1,0,0,0,0;0,(-4/23),(-4/65),(-4/61),1,0,0,0;(-1/4),(-1/23),(-1/65),(-1/61),(-1/57),1,0,0;0,0,0,0,0,(-19/90),1,0;0,0,0,0,0,(-19/90),(-19/251),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/34),1,0,0,0,0,0;0,(-5/34),(-5/131),1,0,0,0,0;0,(-5/34),(-5/131),(-5/126),1,0,0,0;(-1/5),(-1/34),(-1/131),(-1/126),(-1/121),1,0,0;0,0,0,0,0,(-121/701),1,0;0,0,0,0,0,(-121/701),(-121/2683),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/47),1,0,0,0,0,0;0,(-6/47),(-6/229),1,0,0,0,0;0,(-6/47),(-6/229),(-6/223),1,0,0,0;(-1/6),(-1/47),(-1/229),(-1/223),(-1/217),1,0,0;0,0,0,0,0,(-217/1482),1,0;0,0,0,0,0,(-217/1482),(-217/7193),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/62),1,0,0,0,0,0;0,(-7/62),(-7/365),1,0,0,0,0;0,(-7/62),(-7/365),(-7/358),1,0,0,0;(-1/7),(-1/62),(-1/365),(-1/358),(-1/351),1,0,0;0,0,0,0,0,(-117/919),1,0;0,0,0,0,0,(-117/919),(-39/1799),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/79),1,0,0,0,0,0;0,(-8/79),(-8/545),1,0,0,0,0;0,(-8/79),(-8/545),(-8/537),1,0,0,0;(-1/8),(-1/79),(-1/545),(-1/537),(-1/529),1,0,0;0,0,0,0,0,(-529/4694),1,0;0,0,0,0,0,(-529/4694),(-529/32329),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/98),1,0,0,0,0,0;0,(-9/98),(-9/775),1,0,0,0,0;0,(-9/98),(-9/775),(-9/766),1,0,0,0;(-1/9),(-1/98),(-1/775),(-1/766),(-1/757),1,0,0;0,0,0,0,0,(-757/7485),1,0;0,0,0,0,0,(-757/7485),(-757/59123),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/119),1,0,0,0,0,0;0,(-10/119),(-10/1061),1,0,0,0,0;0,(-10/119),(-10/1061),(-10/1051),1,0,0,0;(-1/10),(-1/119),(-1/1061),(-1/1051),(-1/1041),1,0,0;0,0,0,0,0,(-347/3782),1,0;0,0,0,0,0,(-347/3782),(-347/33691),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/142),1,0,0,0,0,0;0,(-11/142),(-11/1409),1,0,0,0,0;0,(-11/142),(-11/1409),(-11/1398),1,0,0,0;(-1/11),(-1/142),(-1/1409),(-1/1398),(-1/1387),1,0,0;0,0,0,0,0,(-1387/16517),1,0;0,0,0,0,0,(-1387/16517),(-1387/163783),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,0,1,0,0;0,(-14/3),1,1,1,(1/3),0,0;0,0,(-25/14),(3/14),(3/14),(1/14),0,0;0,0,0,(-44/25),(6/25),(2/25),0,0;0,0,0,0,(-19/11),(1/11),0,0;0,0,0,0,0,(-69/19),1,1;0,0,0,0,0,0,(-119/69),(19/69);0,0,0,0,0,0,0,(-200/119)],!![-4,1,0,0,0,1,0,0;0,(-23/4),1,1,1,(1/4),0,0;0,0,(-65/23),(4/23),(4/23),(1/23),0,0;0,0,0,(-183/65),(12/65),(3/65),0,0;0,0,0,0,(-171/61),(3/61),0,0;0,0,0,0,0,(-90/19),1,1;0,0,0,0,0,0,(-251/90),(19/90);0,0,0,0,0,0,0,(-696/251)],!![-5,1,0,0,0,1,0,0;0,(-34/5),1,1,1,(1/5),0,0;0,0,(-131/34),(5/34),(5/34),(1/34),0,0;0,0,0,(-504/131),(20/131),(4/131),0,0;0,0,0,0,(-242/63),(2/63),0,0;0,0,0,0,0,(-701/121),1,1;0,0,0,0,0,0,(-2683/701),(121/701);0,0,0,0,0,0,0,(-10248/2683)],!![-6,1,0,0,0,1,0,0;0,(-47/6),1,1,1,(1/6),0,0;0,0,(-229/47),(6/47),(6/47),(1/47),0,0;0,0,0,(-1115/229),(30/229),(5/229),0,0;0,0,0,0,(-1085/223),(5/223),0,0;0,0,0,0,0,(-1482/217),1,1;0,0,0,0,0,0,(-7193/1482),(217/1482);0,0,0,0,0,0,0,(-34880/7193)],!![-7,1,0,0,0,1,0,0;0,(-62/7),1,1,1,(1/7),0,0;0,0,(-365/62),(7/62),(7/62),(1/62),0,0;0,0,0,(-2148/365),(42/365),(6/365),0,0;0,0,0,0,(-1053/179),(3/179),0,0;0,0,0,0,0,(-919/117),1,1;0,0,0,0,0,0,(-5397/919),(117/919);0,0,0,0,0,0,0,(-10560/1799)],!![-8,1,0,0,0,1,0,0;0,(-79/8),1,1,1,(1/8),0,0;0,0,(-545/79),(8/79),(8/79),(1/79),0,0;0,0,0,(-3759/545),(56/545),(7/545),0,0;0,0,0,0,(-3703/537),(7/537),0,0;0,0,0,0,0,(-4694/529),1,1;0,0,0,0,0,0,(-32329/4694),(529/4694);0,0,0,0,0,0,0,(-222600/32329)],!![-9,1,0,0,0,1,0,0;0,(-98/9),1,1,1,(1/9),0,0;0,0,(-775/98),(9/98),(9/98),(1/98),0,0;0,0,0,(-6128/775),(72/775),(8/775),0,0;0,0,0,0,(-3028/383),(4/383),0,0;0,0,0,0,0,(-7485/757),1,1;0,0,0,0,0,0,(-59123/7485),(757/7485);0,0,0,0,0,0,0,(-466928/59123)],!![-10,1,0,0,0,1,0,0;0,(-119/10),1,1,1,(1/10),0,0;0,0,(-1061/119),(10/119),(10/119),(1/119),0,0;0,0,0,(-9459/1061),(90/1061),(9/1061),0,0;0,0,0,0,(-9369/1051),(9/1051),0,0;0,0,0,0,0,(-3782/347),1,1;0,0,0,0,0,0,(-33691/3782),(347/3782);0,0,0,0,0,0,0,(-300096/33691)],!![-11,1,0,0,0,1,0,0;0,(-142/11),1,1,1,(1/11),0,0;0,0,(-1409/142),(11/142),(11/142),(1/142),0,0;0,0,0,(-13980/1409),(110/1409),(10/1409),0,0;0,0,0,0,(-6935/699),(5/699),0,0;0,0,0,0,0,(-16517/1387),1,1;0,0,0,0,0,0,(-163783/16517),(1387/16517);0,0,0,0,0,0,0,(-1623960/163783)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,8,-42,38,-11,1],count := 5,lower := ![(-15/536870912),(128013011/536870912),(439340725/268435456),(2147483641/536870912),(2751401909/536870912)],upper := ![(1/268435456),(32003257/134217728),(878681467/536870912),(1073741829/268435456),(1375700963/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(536870899/536870912)],upper := ![(134217729/134217728)],copies := 3}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((1509918679/268435456) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((188739837/33554432) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum029
