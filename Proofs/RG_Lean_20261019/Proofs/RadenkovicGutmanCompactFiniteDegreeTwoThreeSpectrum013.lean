/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
import Proofs.RadenkovicGutmanRationalSpectralBounds
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum013
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,true,false,true,true],![true,false,true,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,true,false,false],![false,false,false,true,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false]]
noncomputable def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,7,-44,100,-104,52,-12,1]
noncomputable def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/14),1,0,0,0,0;(-1/5),(-1/14),(-1/23),1,0,0,0;0,0,0,(-23/64),1,0,0;(-1/5),(-1/14),(-1/23),(-5/64),(-1/21),1,0;(-1/5),(-1/14),(-1/23),(-5/64),(-1/21),(-5/37),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/23),1,0,0,0,0;(-1/6),(-1/23),(-1/63),1,0,0,0;0,0,0,(-63/241),1,0,0;(-1/6),(-1/23),(-1/63),(-11/241),(-1/60),1,0;(-1/6),(-1/23),(-1/63),(-11/241),(-1/60),(-11/169),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/34),1,0,0,0,0;(-1/7),(-1/34),(-1/129),1,0,0,0;0,0,0,(-129/626),1,0,0;(-1/7),(-1/34),(-1/129),(-19/626),(-1/125),1,0;(-1/7),(-1/34),(-1/129),(-19/626),(-1/125),(-19/481),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/47),1,0,0,0,0;(-1/8),(-1/47),(-1/227),1,0,0,0;0,0,0,(-227/1333),1,0,0;(-1/8),(-1/47),(-1/227),(-29/1333),(-1/222),1,0;(-1/8),(-1/47),(-1/227),(-29/1333),(-1/222),(-29/1081),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/62),1,0,0,0,0;(-1/9),(-1/62),(-1/363),1,0,0,0;0,0,0,(-363/2500),1,0,0;(-1/9),(-1/62),(-1/363),(-41/2500),(-1/357),1,0;(-1/9),(-1/62),(-1/363),(-41/2500),(-1/357),(-41/2101),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/79),1,0,0,0,0;(-1/10),(-1/79),(-1/543),1,0,0,0;0,0,0,(-543/4289),1,0,0;(-1/10),(-1/79),(-1/543),(-55/4289),(-1/536),1,0;(-1/10),(-1/79),(-1/543),(-55/4289),(-1/536),(-55/3697),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;0,(-11/98),1,0,0,0,0;(-1/11),(-1/98),(-1/773),1,0,0,0;0,0,0,(-773/6886),1,0,0;(-1/11),(-1/98),(-1/773),(-71/6886),(-1/765),1,0;(-1/11),(-1/98),(-1/773),(-71/6886),(-1/765),(-71/6049),1],!![1,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0;0,(-12/119),1,0,0,0,0;(-1/12),(-1/119),(-1/1059),1,0,0,0;0,0,0,(-1059/10501),1,0,0;(-1/12),(-1/119),(-1/1059),(-89/10501),(-1/1050),1,0;(-1/12),(-1/119),(-1/1059),(-89/10501),(-1/1050),(-89/9361),1]]
noncomputable def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-5,1,0,1,0,1,1;0,(-14/5),1,(1/5),0,(1/5),(1/5);0,0,(-23/14),(1/14),0,(1/14),(1/14);0,0,0,(-64/23),1,(5/23),(5/23);0,0,0,0,(-105/64),(5/64),(5/64);0,0,0,0,0,(-37/21),(5/21);0,0,0,0,0,0,(-64/37)],!![-6,1,0,1,0,1,1;0,(-23/6),1,(1/6),0,(1/6),(1/6);0,0,(-63/23),(1/23),0,(1/23),(1/23);0,0,0,(-241/63),1,(11/63),(11/63);0,0,0,0,(-660/241),(11/241),(11/241);0,0,0,0,0,(-169/60),(11/60);0,0,0,0,0,0,(-474/169)],!![-7,1,0,1,0,1,1;0,(-34/7),1,(1/7),0,(1/7),(1/7);0,0,(-129/34),(1/34),0,(1/34),(1/34);0,0,0,(-626/129),1,(19/129),(19/129);0,0,0,0,(-2375/626),(19/626),(19/626);0,0,0,0,0,(-481/125),(19/125);0,0,0,0,0,0,(-1848/481)],!![-8,1,0,1,0,1,1;0,(-47/8),1,(1/8),0,(1/8),(1/8);0,0,(-227/47),(1/47),0,(1/47),(1/47);0,0,0,(-1333/227),1,(29/227),(29/227);0,0,0,0,(-6438/1333),(29/1333),(29/1333);0,0,0,0,0,(-1081/222),(29/222);0,0,0,0,0,0,(-5260/1081)],!![-9,1,0,1,0,1,1;0,(-62/9),1,(1/9),0,(1/9),(1/9);0,0,(-363/62),(1/62),0,(1/62),(1/62);0,0,0,(-2500/363),1,(41/363),(41/363);0,0,0,0,(-14637/2500),(41/2500),(41/2500);0,0,0,0,0,(-2101/357),(41/357);0,0,0,0,0,0,(-12360/2101)],!![-10,1,0,1,0,1,1;0,(-79/10),1,(1/10),0,(1/10),(1/10);0,0,(-543/79),(1/79),0,(1/79),(1/79);0,0,0,(-4289/543),1,(55/543),(55/543);0,0,0,0,(-29480/4289),(55/4289),(55/4289);0,0,0,0,0,(-3697/536),(55/536);0,0,0,0,0,0,(-25494/3697)],!![-11,1,0,1,0,1,1;0,(-98/11),1,(1/11),0,(1/11),(1/11);0,0,(-773/98),(1/98),0,(1/98),(1/98);0,0,0,(-6886/773),1,(71/773),(71/773);0,0,0,0,(-54315/6886),(71/6886),(71/6886);0,0,0,0,0,(-6049/765),(71/765);0,0,0,0,0,0,(-47824/6049)],!![-12,1,0,1,0,1,1;0,(-119/12),1,(1/12),0,(1/12),(1/12);0,0,(-1059/119),(1/119),0,(1/119),(1/119);0,0,0,(-10501/1059),1,(89/1059),(89/1059);0,0,0,0,(-93450/10501),(89/10501),(89/10501);0,0,0,0,0,(-9361/1050),(89/1050);0,0,0,0,0,0,(-83448/9361)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-44,100,-104,52,-12,1],count := 7,lower := ![(-1/268435456),(102533219/268435456),(163374539/268435456),(134217727/134217728),(149460461/67108864),(87846643/33554432),(1386267239/268435456)],upper := ![(7/134217728),(51266617/134217728),(81687277/134217728),(268435469/268435456),(597841859/268435456),(702773159/268435456),(693133627/134217728)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((9144499173/1879048192) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((285765609/58720256) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := RationalSpectralBounds.graph_bounds graph boxes boxes_accepted hp
    (2-2/7) (9144499173/1879048192) (285765609/58720256) (by decide +kernel)
  norm_num at h ⊢
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum013
