/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
import Proofs.RadenkovicGutmanRationalSpectralBounds
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum005
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 6 → Fin 6 → Bool := ![![false,true,true,true,true,true],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,false,false],![true,false,false,false,false,false]]
def graph : SimpleGraph (Fin 6) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-6,25,-40,30,-10,1]
def lowerMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;(-1/6),1,0,0,0,0;(-1/6),(-1/11),1,0,0,0;(-1/6),(-1/11),(-1/10),1,0,0;(-1/6),(-1/11),(-1/10),(-1/9),1,0;(-1/6),(-1/11),(-1/10),(-1/9),(-1/8),1],!![1,0,0,0,0,0;(-1/7),1,0,0,0,0;(-1/7),(-1/20),1,0,0,0;(-1/7),(-1/20),(-1/19),1,0,0;(-1/7),(-1/20),(-1/19),(-1/18),1,0;(-1/7),(-1/20),(-1/19),(-1/18),(-1/17),1],!![1,0,0,0,0,0;(-1/8),1,0,0,0,0;(-1/8),(-1/31),1,0,0,0;(-1/8),(-1/31),(-1/30),1,0,0;(-1/8),(-1/31),(-1/30),(-1/29),1,0;(-1/8),(-1/31),(-1/30),(-1/29),(-1/28),1],!![1,0,0,0,0,0;(-1/9),1,0,0,0,0;(-1/9),(-1/44),1,0,0,0;(-1/9),(-1/44),(-1/43),1,0,0;(-1/9),(-1/44),(-1/43),(-1/42),1,0;(-1/9),(-1/44),(-1/43),(-1/42),(-1/41),1],!![1,0,0,0,0,0;(-1/10),1,0,0,0,0;(-1/10),(-1/59),1,0,0,0;(-1/10),(-1/59),(-1/58),1,0,0;(-1/10),(-1/59),(-1/58),(-1/57),1,0;(-1/10),(-1/59),(-1/58),(-1/57),(-1/56),1],!![1,0,0,0,0,0;(-1/11),1,0,0,0,0;(-1/11),(-1/76),1,0,0,0;(-1/11),(-1/76),(-1/75),1,0,0;(-1/11),(-1/76),(-1/75),(-1/74),1,0;(-1/11),(-1/76),(-1/75),(-1/74),(-1/73),1],!![1,0,0,0,0,0;(-1/12),1,0,0,0,0;(-1/12),(-1/95),1,0,0,0;(-1/12),(-1/95),(-1/94),1,0,0;(-1/12),(-1/95),(-1/94),(-1/93),1,0;(-1/12),(-1/95),(-1/94),(-1/93),(-1/92),1]]
def upperMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![-6,1,1,1,1,1;0,(-11/6),(1/6),(1/6),(1/6),(1/6);0,0,(-20/11),(2/11),(2/11),(2/11);0,0,0,(-9/5),(1/5),(1/5);0,0,0,0,(-16/9),(2/9);0,0,0,0,0,(-7/4)],!![-7,1,1,1,1,1;0,(-20/7),(1/7),(1/7),(1/7),(1/7);0,0,(-57/20),(3/20),(3/20),(3/20);0,0,0,(-54/19),(3/19),(3/19);0,0,0,0,(-17/6),(1/6);0,0,0,0,0,(-48/17)],!![-8,1,1,1,1,1;0,(-31/8),(1/8),(1/8),(1/8),(1/8);0,0,(-120/31),(4/31),(4/31),(4/31);0,0,0,(-58/15),(2/15),(2/15);0,0,0,0,(-112/29),(4/29);0,0,0,0,0,(-27/7)],!![-9,1,1,1,1,1;0,(-44/9),(1/9),(1/9),(1/9),(1/9);0,0,(-215/44),(5/44),(5/44),(5/44);0,0,0,(-210/43),(5/43),(5/43);0,0,0,0,(-205/42),(5/42);0,0,0,0,0,(-200/41)],!![-10,1,1,1,1,1;0,(-59/10),(1/10),(1/10),(1/10),(1/10);0,0,(-348/59),(6/59),(6/59),(6/59);0,0,0,(-171/29),(3/29),(3/29);0,0,0,0,(-112/19),(2/19);0,0,0,0,0,(-165/28)],!![-11,1,1,1,1,1;0,(-76/11),(1/11),(1/11),(1/11),(1/11);0,0,(-525/76),(7/76),(7/76),(7/76);0,0,0,(-518/75),(7/75),(7/75);0,0,0,0,(-511/74),(7/74);0,0,0,0,0,(-504/73)],!![-12,1,1,1,1,1;0,(-95/12),(1/12),(1/12),(1/12),(1/12);0,0,(-752/95),(8/95),(8/95),(8/95);0,0,0,(-372/47),(4/47),(4/47);0,0,0,0,(-736/93),(8/93);0,0,0,0,0,(-182/23)]]
theorem matrix_certificates : ∀ k : Fin 7,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-6,1],count := 2,lower := ![(-3/268435456),(201326591/33554432)],upper := ![(5/134217728),(1610612741/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217725/134217728)],upper := ![(268435463/268435456)],copies := 4}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((436207613/100663296) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/6) ∧
    stopLoss (laplacianSpectrum graph) (2-2/6) ≤ ((3489660943/805306368) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := RationalSpectralBounds.graph_bounds graph boxes boxes_accepted hp
    (2-2/6) (436207613/100663296) (3489660943/805306368) (by decide +kernel)
  norm_num at h ⊢
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum005
