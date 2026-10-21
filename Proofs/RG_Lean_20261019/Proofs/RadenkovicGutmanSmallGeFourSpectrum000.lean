/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum000
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,true,true,true,true,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,true],![false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by decide +kernel
  loopless := by decide +kernel
instance : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-40,87,-92,49,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;(-1/6),(-1/11),1,0,0,0,0;(-1/6),(-1/11),(-1/10),1,0,0,0;(-1/6),(-1/11),(-1/10),(-1/9),1,0,0;(-1/6),(-1/11),(-1/10),(-1/9),(-1/8),1,0;0,0,0,0,0,(-4/11),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;(-1/7),(-1/20),1,0,0,0,0;(-1/7),(-1/20),(-1/19),1,0,0,0;(-1/7),(-1/20),(-1/19),(-1/18),1,0,0;(-1/7),(-1/20),(-1/19),(-1/18),(-1/17),1,0;0,0,0,0,0,(-17/65),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;(-1/8),(-1/31),1,0,0,0,0;(-1/8),(-1/31),(-1/30),1,0,0,0;(-1/8),(-1/31),(-1/30),(-1/29),1,0,0;(-1/8),(-1/31),(-1/30),(-1/29),(-1/28),1,0;0,0,0,0,0,(-7/34),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;(-1/9),(-1/44),1,0,0,0,0;(-1/9),(-1/44),(-1/43),1,0,0,0;(-1/9),(-1/44),(-1/43),(-1/42),1,0,0;(-1/9),(-1/44),(-1/43),(-1/42),(-1/41),1,0;0,0,0,0,0,(-41/241),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;(-1/10),(-1/59),1,0,0,0,0;(-1/10),(-1/59),(-1/58),1,0,0,0;(-1/10),(-1/59),(-1/58),(-1/57),1,0,0;(-1/10),(-1/59),(-1/58),(-1/57),(-1/56),1,0;0,0,0,0,0,(-28/193),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;(-1/11),(-1/76),1,0,0,0,0;(-1/11),(-1/76),(-1/75),1,0,0,0;(-1/11),(-1/76),(-1/75),(-1/74),1,0,0;(-1/11),(-1/76),(-1/75),(-1/74),(-1/73),1,0;0,0,0,0,0,(-73/577),1],!![1,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0;(-1/12),(-1/95),1,0,0,0,0;(-1/12),(-1/95),(-1/94),1,0,0,0;(-1/12),(-1/95),(-1/94),(-1/93),1,0,0;(-1/12),(-1/95),(-1/94),(-1/93),(-1/92),1,0;0,0,0,0,0,(-23/205),1],!![1,0,0,0,0,0,0;(-1/13),1,0,0,0,0,0;(-1/13),(-1/116),1,0,0,0,0;(-1/13),(-1/116),(-1/115),1,0,0,0;(-1/13),(-1/116),(-1/115),(-1/114),1,0,0;(-1/13),(-1/116),(-1/115),(-1/114),(-1/113),1,0;0,0,0,0,0,(-113/1121),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-6,1,1,1,1,1,0;0,(-11/6),(1/6),(1/6),(1/6),(1/6),0;0,0,(-20/11),(2/11),(2/11),(2/11),0;0,0,0,(-9/5),(1/5),(1/5),0;0,0,0,0,(-16/9),(2/9),0;0,0,0,0,0,(-11/4),1;0,0,0,0,0,0,(-18/11)],!![-7,1,1,1,1,1,0;0,(-20/7),(1/7),(1/7),(1/7),(1/7),0;0,0,(-57/20),(3/20),(3/20),(3/20),0;0,0,0,(-54/19),(3/19),(3/19),0;0,0,0,0,(-17/6),(1/6),0;0,0,0,0,0,(-65/17),1;0,0,0,0,0,0,(-178/65)],!![-8,1,1,1,1,1,0;0,(-31/8),(1/8),(1/8),(1/8),(1/8),0;0,0,(-120/31),(4/31),(4/31),(4/31),0;0,0,0,(-58/15),(2/15),(2/15),0;0,0,0,0,(-112/29),(4/29),0;0,0,0,0,0,(-34/7),1;0,0,0,0,0,0,(-129/34)],!![-9,1,1,1,1,1,0;0,(-44/9),(1/9),(1/9),(1/9),(1/9),0;0,0,(-215/44),(5/44),(5/44),(5/44),0;0,0,0,(-210/43),(5/43),(5/43),0;0,0,0,0,(-205/42),(5/42),0;0,0,0,0,0,(-241/41),1;0,0,0,0,0,0,(-1164/241)],!![-10,1,1,1,1,1,0;0,(-59/10),(1/10),(1/10),(1/10),(1/10),0;0,0,(-348/59),(6/59),(6/59),(6/59),0;0,0,0,(-171/29),(3/29),(3/29),0;0,0,0,0,(-112/19),(2/19),0;0,0,0,0,0,(-193/28),1;0,0,0,0,0,0,(-1130/193)],!![-11,1,1,1,1,1,0;0,(-76/11),(1/11),(1/11),(1/11),(1/11),0;0,0,(-525/76),(7/76),(7/76),(7/76),0;0,0,0,(-518/75),(7/75),(7/75),0;0,0,0,0,(-511/74),(7/74),0;0,0,0,0,0,(-577/73),1;0,0,0,0,0,0,(-3966/577)],!![-12,1,1,1,1,1,0;0,(-95/12),(1/12),(1/12),(1/12),(1/12),0;0,0,(-752/95),(8/95),(8/95),(8/95),0;0,0,0,(-372/47),(4/47),(4/47),0;0,0,0,0,(-736/93),(8/93),0;0,0,0,0,0,(-205/23),1;0,0,0,0,0,0,(-1617/205)],!![-13,1,1,1,1,1,0;0,(-116/13),(1/13),(1/13),(1/13),(1/13),0;0,0,(-1035/116),(9/116),(9/116),(9/116),0;0,0,0,(-1026/115),(9/115),(9/115),0;0,0,0,0,(-339/38),(3/38),0;0,0,0,0,0,(-1121/113),1;0,0,0,0,0,0,(-9976/1121)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-7,19,-9,1],count := 4,lower := ![(-1/268435456),(125072069/268435456),(666443609/268435456),(1624403399/268435456)],upper := ![(7/134217728),(31268021/67108864),(83305453/33554432),(812201707/134217728)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 3}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor]
  <;> ring
theorem actual_graph_bounds :
    ((299796191/58720256) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((4796739161/939524096) : ℝ) := by
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted
    (graph_charpoly.trans factorization) (2-2/7)
  norm_num [boxes,FactoredRoots.lowerTotal,FactoredRoots.upperTotal,FactoredRoots.lower,
    FactoredRoots.upper,Fin.sum_univ_succ] at h
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum000
