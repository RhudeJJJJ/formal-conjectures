/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum027
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,true,true,true,true,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,true,true],![false,false,false,false,false,true,false,false],![false,false,false,false,false,true,false,false]]
noncomputable def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,-8,57,-158,223,-172,71,-14,1]
noncomputable def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;(-1/6),(-1/11),1,0,0,0,0,0;(-1/6),(-1/11),(-1/10),1,0,0,0,0;(-1/6),(-1/11),(-1/10),(-1/9),1,0,0,0;(-1/6),(-1/11),(-1/10),(-1/9),(-1/8),1,0,0;0,0,0,0,0,(-4/15),1,0;0,0,0,0,0,(-4/15),(-2/13),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;(-1/7),(-1/20),1,0,0,0,0,0;(-1/7),(-1/20),(-1/19),1,0,0,0,0;(-1/7),(-1/20),(-1/19),(-1/18),1,0,0,0;(-1/7),(-1/20),(-1/19),(-1/18),(-1/17),1,0,0;0,0,0,0,0,(-17/82),1,0;0,0,0,0,0,(-17/82),(-17/229),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;(-1/8),(-1/31),1,0,0,0,0,0;(-1/8),(-1/31),(-1/30),1,0,0,0,0;(-1/8),(-1/31),(-1/30),(-1/29),1,0,0,0;(-1/8),(-1/31),(-1/30),(-1/29),(-1/28),1,0,0;0,0,0,0,0,(-7/41),1,0;0,0,0,0,0,(-7/41),(-7/157),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;(-1/9),(-1/44),1,0,0,0,0,0;(-1/9),(-1/44),(-1/43),1,0,0,0,0;(-1/9),(-1/44),(-1/43),(-1/42),1,0,0,0;(-1/9),(-1/44),(-1/43),(-1/42),(-1/41),1,0,0;0,0,0,0,0,(-41/282),1,0;0,0,0,0,0,(-41/282),(-41/1369),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;(-1/10),(-1/59),1,0,0,0,0,0;(-1/10),(-1/59),(-1/58),1,0,0,0,0;(-1/10),(-1/59),(-1/58),(-1/57),1,0,0,0;(-1/10),(-1/59),(-1/58),(-1/57),(-1/56),1,0,0;0,0,0,0,0,(-28/221),1,0;0,0,0,0,0,(-28/221),(-14/649),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;(-1/11),(-1/76),1,0,0,0,0,0;(-1/11),(-1/76),(-1/75),1,0,0,0,0;(-1/11),(-1/76),(-1/75),(-1/74),1,0,0,0;(-1/11),(-1/76),(-1/75),(-1/74),(-1/73),1,0,0;0,0,0,0,0,(-73/650),1,0;0,0,0,0,0,(-73/650),(-73/4477),1],!![1,0,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0,0;(-1/12),(-1/95),1,0,0,0,0,0;(-1/12),(-1/95),(-1/94),1,0,0,0,0;(-1/12),(-1/95),(-1/94),(-1/93),1,0,0,0;(-1/12),(-1/95),(-1/94),(-1/93),(-1/92),1,0,0;0,0,0,0,0,(-23/228),1,0;0,0,0,0,0,(-23/228),(-23/1801),1],!![1,0,0,0,0,0,0,0;(-1/13),1,0,0,0,0,0,0;(-1/13),(-1/116),1,0,0,0,0,0;(-1/13),(-1/116),(-1/115),1,0,0,0,0;(-1/13),(-1/116),(-1/115),(-1/114),1,0,0,0;(-1/13),(-1/116),(-1/115),(-1/114),(-1/113),1,0,0;0,0,0,0,0,(-113/1234),1,0;0,0,0,0,0,(-113/1234),(-113/10993),1],!![1,0,0,0,0,0,0,0;(-1/14),1,0,0,0,0,0,0;(-1/14),(-1/139),1,0,0,0,0,0;(-1/14),(-1/139),(-1/138),1,0,0,0,0;(-1/14),(-1/139),(-1/138),(-1/137),1,0,0,0;(-1/14),(-1/139),(-1/138),(-1/137),(-1/136),1,0,0;0,0,0,0,0,(-68/811),1,0;0,0,0,0,0,(-68/811),(-34/4021),1]]
noncomputable def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-6,1,1,1,1,1,0,0;0,(-11/6),(1/6),(1/6),(1/6),(1/6),0,0;0,0,(-20/11),(2/11),(2/11),(2/11),0,0;0,0,0,(-9/5),(1/5),(1/5),0,0;0,0,0,0,(-16/9),(2/9),0,0;0,0,0,0,0,(-15/4),1,1;0,0,0,0,0,0,(-26/15),(4/15);0,0,0,0,0,0,0,(-22/13)],!![-7,1,1,1,1,1,0,0;0,(-20/7),(1/7),(1/7),(1/7),(1/7),0,0;0,0,(-57/20),(3/20),(3/20),(3/20),0,0;0,0,0,(-54/19),(3/19),(3/19),0,0;0,0,0,0,(-17/6),(1/6),0,0;0,0,0,0,0,(-82/17),1,1;0,0,0,0,0,0,(-229/82),(17/82);0,0,0,0,0,0,0,(-636/229)],!![-8,1,1,1,1,1,0,0;0,(-31/8),(1/8),(1/8),(1/8),(1/8),0,0;0,0,(-120/31),(4/31),(4/31),(4/31),0,0;0,0,0,(-58/15),(2/15),(2/15),0,0;0,0,0,0,(-112/29),(4/29),0,0;0,0,0,0,0,(-41/7),1,1;0,0,0,0,0,0,(-157/41),(7/41);0,0,0,0,0,0,0,(-600/157)],!![-9,1,1,1,1,1,0,0;0,(-44/9),(1/9),(1/9),(1/9),(1/9),0,0;0,0,(-215/44),(5/44),(5/44),(5/44),0,0;0,0,0,(-210/43),(5/43),(5/43),0,0;0,0,0,0,(-205/42),(5/42),0,0;0,0,0,0,0,(-282/41),1,1;0,0,0,0,0,0,(-1369/282),(41/282);0,0,0,0,0,0,0,(-6640/1369)],!![-10,1,1,1,1,1,0,0;0,(-59/10),(1/10),(1/10),(1/10),(1/10),0,0;0,0,(-348/59),(6/59),(6/59),(6/59),0,0;0,0,0,(-171/29),(3/29),(3/29),0,0;0,0,0,0,(-112/19),(2/19),0,0;0,0,0,0,0,(-221/28),1,1;0,0,0,0,0,0,(-1298/221),(28/221);0,0,0,0,0,0,0,(-3810/649)],!![-11,1,1,1,1,1,0,0;0,(-76/11),(1/11),(1/11),(1/11),(1/11),0,0;0,0,(-525/76),(7/76),(7/76),(7/76),0,0;0,0,0,(-518/75),(7/75),(7/75),0,0;0,0,0,0,(-511/74),(7/74),0,0;0,0,0,0,0,(-650/73),1,1;0,0,0,0,0,0,(-4477/650),(73/650);0,0,0,0,0,0,0,(-30828/4477)],!![-12,1,1,1,1,1,0,0;0,(-95/12),(1/12),(1/12),(1/12),(1/12),0,0;0,0,(-752/95),(8/95),(8/95),(8/95),0,0;0,0,0,(-372/47),(4/47),(4/47),0,0;0,0,0,0,(-736/93),(8/93),0,0;0,0,0,0,0,(-228/23),1,1;0,0,0,0,0,0,(-1801/228),(23/228);0,0,0,0,0,0,0,(-14224/1801)],!![-13,1,1,1,1,1,0,0;0,(-116/13),(1/13),(1/13),(1/13),(1/13),0,0;0,0,(-1035/116),(9/116),(9/116),(9/116),0,0;0,0,0,(-1026/115),(9/115),(9/115),0,0;0,0,0,0,(-339/38),(3/38),0,0;0,0,0,0,0,(-1234/113),1,1;0,0,0,0,0,0,(-10993/1234),(113/1234);0,0,0,0,0,0,0,(-97920/10993)],!![-14,1,1,1,1,1,0,0;0,(-139/14),(1/14),(1/14),(1/14),(1/14),0,0;0,0,(-1380/139),(10/139),(10/139),(10/139),0,0;0,0,0,(-685/69),(5/69),(5/69),0,0;0,0,0,0,(-1360/137),(10/137),0,0;0,0,0,0,0,(-811/68),1,1;0,0,0,0,0,0,(-8042/811),(68/811);0,0,0,0,0,0,0,(-39870/4021)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,25,-10,1],count := 4,lower := ![(-15/536870912),(100341685/268435456),(1870921011/536870912),(1648552357/268435456)],upper := ![(1/268435456),(200683387/536870912),(467730257/134217728),(3297104731/536870912)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(536870899/536870912)],upper := ![(134217729/134217728)],copies := 4}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((3288977533/536870912) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((3288977567/536870912) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum027
