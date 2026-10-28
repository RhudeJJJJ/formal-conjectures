/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum012
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,false,false,true,false],![true,false,true,true,true,false,false],![false,true,false,false,false,false,false],![false,true,false,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,false,false,true],![false,false,false,false,false,true,false]]
noncomputable def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,7,-46,102,-104,52,-12,1]
noncomputable def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0;0,(-3/14),1,0,0,0,0;0,(-3/14),(-3/25),1,0,0,0;0,(-3/14),(-3/25),(-3/22),1,0,0;(-1/3),(-1/14),(-1/25),(-1/22),(-1/19),1,0;0,0,0,0,0,(-19/50),1],!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/23),1,0,0,0,0;0,(-4/23),(-4/65),1,0,0,0;0,(-4/23),(-4/65),(-4/61),1,0,0;(-1/4),(-1/23),(-1/65),(-1/61),(-1/57),1,0;0,0,0,0,0,(-19/71),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/34),1,0,0,0,0;0,(-5/34),(-5/131),1,0,0,0;0,(-5/34),(-5/131),(-5/126),1,0,0;(-1/5),(-1/34),(-1/131),(-1/126),(-1/121),1,0;0,0,0,0,0,(-121/580),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/47),1,0,0,0,0;0,(-6/47),(-6/229),1,0,0,0;0,(-6/47),(-6/229),(-6/223),1,0,0;(-1/6),(-1/47),(-1/229),(-1/223),(-1/217),1,0;0,0,0,0,0,(-217/1265),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/62),1,0,0,0,0;0,(-7/62),(-7/365),1,0,0,0;0,(-7/62),(-7/365),(-7/358),1,0,0;(-1/7),(-1/62),(-1/365),(-1/358),(-1/351),1,0;0,0,0,0,0,(-117/802),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/79),1,0,0,0,0;0,(-8/79),(-8/545),1,0,0,0;0,(-8/79),(-8/545),(-8/537),1,0,0;(-1/8),(-1/79),(-1/545),(-1/537),(-1/529),1,0;0,0,0,0,0,(-529/4165),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/98),1,0,0,0,0;0,(-9/98),(-9/775),1,0,0,0;0,(-9/98),(-9/775),(-9/766),1,0,0;(-1/9),(-1/98),(-1/775),(-1/766),(-1/757),1,0;0,0,0,0,0,(-757/6728),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/119),1,0,0,0,0;0,(-10/119),(-10/1061),1,0,0,0;0,(-10/119),(-10/1061),(-10/1051),1,0,0;(-1/10),(-1/119),(-1/1061),(-1/1051),(-1/1041),1,0;0,0,0,0,0,(-347/3435),1]]
noncomputable def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-3,1,0,0,0,1,0;0,(-14/3),1,1,1,(1/3),0;0,0,(-25/14),(3/14),(3/14),(1/14),0;0,0,0,(-44/25),(6/25),(2/25),0;0,0,0,0,(-19/11),(1/11),0;0,0,0,0,0,(-50/19),1;0,0,0,0,0,0,(-81/50)],!![-4,1,0,0,0,1,0;0,(-23/4),1,1,1,(1/4),0;0,0,(-65/23),(4/23),(4/23),(1/23),0;0,0,0,(-183/65),(12/65),(3/65),0;0,0,0,0,(-171/61),(3/61),0;0,0,0,0,0,(-71/19),1;0,0,0,0,0,0,(-194/71)],!![-5,1,0,0,0,1,0;0,(-34/5),1,1,1,(1/5),0;0,0,(-131/34),(5/34),(5/34),(1/34),0;0,0,0,(-504/131),(20/131),(4/131),0;0,0,0,0,(-242/63),(2/63),0;0,0,0,0,0,(-580/121),1;0,0,0,0,0,0,(-2199/580)],!![-6,1,0,0,0,1,0;0,(-47/6),1,1,1,(1/6),0;0,0,(-229/47),(6/47),(6/47),(1/47),0;0,0,0,(-1115/229),(30/229),(5/229),0;0,0,0,0,(-1085/223),(5/223),0;0,0,0,0,0,(-1265/217),1;0,0,0,0,0,0,(-6108/1265)],!![-7,1,0,0,0,1,0;0,(-62/7),1,1,1,(1/7),0;0,0,(-365/62),(7/62),(7/62),(1/62),0;0,0,0,(-2148/365),(42/365),(6/365),0;0,0,0,0,(-1053/179),(3/179),0;0,0,0,0,0,(-802/117),1;0,0,0,0,0,0,(-4695/802)],!![-8,1,0,0,0,1,0;0,(-79/8),1,1,1,(1/8),0;0,0,(-545/79),(8/79),(8/79),(1/79),0;0,0,0,(-3759/545),(56/545),(7/545),0;0,0,0,0,(-3703/537),(7/537),0;0,0,0,0,0,(-4165/529),1;0,0,0,0,0,0,(-28626/4165)],!![-9,1,0,0,0,1,0;0,(-98/9),1,1,1,(1/9),0;0,0,(-775/98),(9/98),(9/98),(1/98),0;0,0,0,(-6128/775),(72/775),(8/775),0;0,0,0,0,(-3028/383),(4/383),0;0,0,0,0,0,(-6728/757),1;0,0,0,0,0,0,(-53067/6728)],!![-10,1,0,0,0,1,0;0,(-119/10),1,1,1,(1/10),0;0,0,(-1061/119),(10/119),(10/119),(1/119),0;0,0,0,(-9459/1061),(90/1061),(9/1061),0;0,0,0,0,(-9369/1051),(9/1051),0;0,0,0,0,0,(-3435/347),1;0,0,0,0,0,0,(-30568/3435)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-32,31,-10,1],count := 5,lower := ![(-1/268435456),(79331309/268435456),(200128927/134217728),(418341067/134217728),(684041617/134217728)],upper := ![(7/134217728),(19832831/67108864),(400257869/268435456),(836682149/268435456),(1368083249/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((1123863329/234881024) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((4495453421/939524096) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum012
