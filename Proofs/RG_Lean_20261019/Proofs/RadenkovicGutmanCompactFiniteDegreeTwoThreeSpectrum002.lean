/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
import Proofs.RadenkovicGutmanRationalSpectralBounds
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum002
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 6 → Fin 6 → Bool := ![![false,true,true,true,true,false],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,false,true],![false,false,false,false,true,false]]
noncomputable def graph : SimpleGraph (Fin 6) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,-6,28,-46,33,-10,1]
noncomputable def lowerMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;(-1/5),1,0,0,0,0;(-1/5),(-1/9),1,0,0,0;(-1/5),(-1/9),(-1/8),1,0,0;(-1/5),(-1/9),(-1/8),(-1/7),1,0;0,0,0,0,(-7/19),1],!![1,0,0,0,0,0;(-1/6),1,0,0,0,0;(-1/6),(-1/17),1,0,0,0;(-1/6),(-1/17),(-1/16),1,0,0;(-1/6),(-1/17),(-1/16),(-1/15),1,0;0,0,0,0,(-5/19),1],!![1,0,0,0,0,0;(-1/7),1,0,0,0,0;(-1/7),(-1/27),1,0,0,0;(-1/7),(-1/27),(-1/26),1,0,0;(-1/7),(-1/27),(-1/26),(-1/25),1,0;0,0,0,0,(-25/121),1],!![1,0,0,0,0,0;(-1/8),1,0,0,0,0;(-1/8),(-1/39),1,0,0,0;(-1/8),(-1/39),(-1/38),1,0,0;(-1/8),(-1/39),(-1/38),(-1/37),1,0;0,0,0,0,(-37/217),1],!![1,0,0,0,0,0;(-1/9),1,0,0,0,0;(-1/9),(-1/53),1,0,0,0;(-1/9),(-1/53),(-1/52),1,0,0;(-1/9),(-1/53),(-1/52),(-1/51),1,0;0,0,0,0,(-17/117),1],!![1,0,0,0,0,0;(-1/10),1,0,0,0,0;(-1/10),(-1/69),1,0,0,0;(-1/10),(-1/69),(-1/68),1,0,0;(-1/10),(-1/69),(-1/68),(-1/67),1,0;0,0,0,0,(-67/529),1],!![1,0,0,0,0,0;(-1/11),1,0,0,0,0;(-1/11),(-1/87),1,0,0,0;(-1/11),(-1/87),(-1/86),1,0,0;(-1/11),(-1/87),(-1/86),(-1/85),1,0;0,0,0,0,(-85/757),1]]
noncomputable def upperMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![-5,1,1,1,1,0;0,(-9/5),(1/5),(1/5),(1/5),0;0,0,(-16/9),(2/9),(2/9),0;0,0,0,(-7/4),(1/4),0;0,0,0,0,(-19/7),1;0,0,0,0,0,(-31/19)],!![-6,1,1,1,1,0;0,(-17/6),(1/6),(1/6),(1/6),0;0,0,(-48/17),(3/17),(3/17),0;0,0,0,(-45/16),(3/16),0;0,0,0,0,(-19/5),1;0,0,0,0,0,(-52/19)],!![-7,1,1,1,1,0;0,(-27/7),(1/7),(1/7),(1/7),0;0,0,(-104/27),(4/27),(4/27),0;0,0,0,(-50/13),(2/13),0;0,0,0,0,(-121/25),1;0,0,0,0,0,(-459/121)],!![-8,1,1,1,1,0;0,(-39/8),(1/8),(1/8),(1/8),0;0,0,(-190/39),(5/39),(5/39),0;0,0,0,(-185/38),(5/38),0;0,0,0,0,(-217/37),1;0,0,0,0,0,(-1048/217)],!![-9,1,1,1,1,0;0,(-53/9),(1/9),(1/9),(1/9),0;0,0,(-312/53),(6/53),(6/53),0;0,0,0,(-153/26),(3/26),0;0,0,0,0,(-117/17),1;0,0,0,0,0,(-685/117)],!![-10,1,1,1,1,0;0,(-69/10),(1/10),(1/10),(1/10),0;0,0,(-476/69),(7/69),(7/69),0;0,0,0,(-469/68),(7/68),0;0,0,0,0,(-529/67),1;0,0,0,0,0,(-3636/529)],!![-11,1,1,1,1,0;0,(-87/11),(1/11),(1/11),(1/11),0;0,0,(-688/87),(8/87),(8/87),0;0,0,0,(-340/43),(4/43),0;0,0,0,0,(-757/85),1;0,0,0,0,0,(-5971/757)]]
theorem matrix_certificates : ∀ k : Fin 7,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,-6,16,-8,1],count := 4,lower := ![(-3/268435456),(65211437/134217728),(651763083/268435456),(1365297671/268435456)],upper := ![(5/134217728),(130422887/268435456),(81470387/33554432),(341324421/67108864)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217725/134217728)],upper := ![(268435463/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((1683413851/402653184) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/6) ∧
    stopLoss (laplacianSpectrum graph) (2-2/6) ≤ ((841706945/201326592) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := RationalSpectralBounds.graph_bounds graph boxes boxes_accepted hp
    (2-2/6) (1683413851/402653184) (841706945/201326592) (by decide +kernel)
  norm_num at h ⊢
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum002
