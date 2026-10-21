/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum009
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,true,true,false,false],![true,false,true,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,true,false],![false,false,false,false,true,false,true],![false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-50,115,-114,54,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/11),1,0,0,0,0;(-1/4),(-1/11),(-1/18),1,0,0,0;(-1/4),(-1/11),(-1/18),(-5/31),1,0,0;0,0,0,0,(-31/83),1,0;0,0,0,0,0,(-83/218),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/19),1,0,0,0,0;(-1/5),(-1/19),(-1/52),1,0,0,0;(-1/5),(-1/19),(-1/52),(-11/145),1,0,0;0,0,0,0,(-145/547),1,0;0,0,0,0,0,(-547/2043),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/29),1,0,0,0,0;(-1/6),(-1/29),(-1/110),1,0,0,0;(-1/6),(-1/29),(-1/110),(-19/421),1,0,0;0,0,0,0,(-421/2029),1,0;0,0,0,0,0,(-2029/9724),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/41),1,0,0,0,0;(-1/7),(-1/41),(-1/198),1,0,0,0;(-1/7),(-1/41),(-1/198),(-29/961),1,0,0;0,0,0,0,(-961/5621),1,0;0,0,0,0,0,(-5621/32765),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/55),1,0,0,0,0;(-1/8),(-1/55),(-1/322),1,0,0,0;(-1/8),(-1/55),(-1/322),(-41/1891),1,0,0;0,0,0,0,(-1891/12991),1,0;0,0,0,0,0,(-12991/89046),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/71),1,0,0,0,0;(-1/9),(-1/71),(-1/488),1,0,0,0;(-1/9),(-1/71),(-1/488),(-55/3361),1,0,0;0,0,0,0,(-3361/26503),1,0;0,0,0,0,0,(-26503/208663),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/89),1,0,0,0,0;(-1/10),(-1/89),(-1/702),1,0,0,0;(-1/10),(-1/89),(-1/702),(-71/5545),1,0,0;0,0,0,0,(-5545/49337),1,0;0,0,0,0,0,(-49337/438488),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;0,(-11/109),1,0,0,0,0;(-1/11),(-1/109),(-1/970),1,0,0,0;(-1/11),(-1/109),(-1/970),(-89/8641),1,0,0;0,0,0,0,(-8641/85609),1,0;0,0,0,0,0,(-85609/847449),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-4,1,0,1,1,0,0;0,(-11/4),1,(1/4),(1/4),0,0;0,0,(-18/11),(1/11),(1/11),0,0;0,0,0,(-31/18),(5/18),0,0;0,0,0,0,(-83/31),1,0;0,0,0,0,0,(-218/83),1;0,0,0,0,0,0,(-353/218)],!![-5,1,0,1,1,0,0;0,(-19/5),1,(1/5),(1/5),0,0;0,0,(-52/19),(1/19),(1/19),0,0;0,0,0,(-145/52),(11/52),0,0;0,0,0,0,(-547/145),1,0;0,0,0,0,0,(-2043/547),1;0,0,0,0,0,0,(-5582/2043)],!![-6,1,0,1,1,0,0;0,(-29/6),1,(1/6),(1/6),0,0;0,0,(-110/29),(1/29),(1/29),0,0;0,0,0,(-421/110),(19/110),0,0;0,0,0,0,(-2029/421),1,0;0,0,0,0,0,(-9724/2029),1;0,0,0,0,0,0,(-36867/9724)],!![-7,1,0,1,1,0,0;0,(-41/7),1,(1/7),(1/7),0,0;0,0,(-198/41),(1/41),(1/41),0,0;0,0,0,(-961/198),(29/198),0,0;0,0,0,0,(-5621/961),1,0;0,0,0,0,0,(-32765/5621),1;0,0,0,0,0,0,(-158204/32765)],!![-8,1,0,1,1,0,0;0,(-55/8),1,(1/8),(1/8),0,0;0,0,(-322/55),(1/55),(1/55),0,0;0,0,0,(-1891/322),(41/322),0,0;0,0,0,0,(-12991/1891),1,0;0,0,0,0,0,(-89046/12991),1;0,0,0,0,0,0,(-521285/89046)],!![-9,1,0,1,1,0,0;0,(-71/9),1,(1/9),(1/9),0,0;0,0,(-488/71),(1/71),(1/71),0,0;0,0,0,(-3361/488),(55/488),0,0;0,0,0,0,(-26503/3361),1,0;0,0,0,0,0,(-208663/26503),1;0,0,0,0,0,0,(-1434138/208663)],!![-10,1,0,1,1,0,0;0,(-89/10),1,(1/10),(1/10),0,0;0,0,(-702/89),(1/89),(1/89),0,0;0,0,0,(-5545/702),(71/702),0,0;0,0,0,0,(-49337/5545),1,0;0,0,0,0,0,(-438488/49337),1;0,0,0,0,0,0,(-3458567/438488)],!![-11,1,0,1,1,0,0;0,(-109/11),1,(1/11),(1/11),0,0;0,0,(-970/109),(1/109),(1/109),0,0;0,0,0,(-8641/970),(89/970),0,0;0,0,0,0,(-85609/8641),1,0;0,0,0,0,0,(-847449/85609),1;0,0,0,0,0,0,(-7541432/847449)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-50,115,-114,54,-12,1],count := 7,lower := ![(-1/268435456),(69879839/268435456),(168097049/268435456),(377279789/268435456),(610477259/268435456),(832038419/268435456),(290863271/67108864)],upper := ![(7/134217728),(34939927/134217728),(21012133/33554432),(94319951/67108864),(305238637/134217728),(416019217/134217728),(1163453099/268435456)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((4289052459/939524096) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((8578105233/1879048192) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum009
