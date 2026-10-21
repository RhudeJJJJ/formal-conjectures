/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum011
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,true,true,true,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,true,true],![false,false,false,false,true,false,false],![false,false,false,false,true,false,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-42,93,-98,51,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;(-1/5),(-1/9),1,0,0,0,0;(-1/5),(-1/9),(-1/8),1,0,0,0;(-1/5),(-1/9),(-1/8),(-1/7),1,0,0;0,0,0,0,(-7/26),1,0;0,0,0,0,(-7/26),(-7/45),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;(-1/6),(-1/17),1,0,0,0,0;(-1/6),(-1/17),(-1/16),1,0,0,0;(-1/6),(-1/17),(-1/16),(-1/15),1,0,0;0,0,0,0,(-5/24),1,0;0,0,0,0,(-5/24),(-5/67),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;(-1/7),(-1/27),1,0,0,0,0;(-1/7),(-1/27),(-1/26),1,0,0,0;(-1/7),(-1/27),(-1/26),(-1/25),1,0,0;0,0,0,0,(-25/146),1,0;0,0,0,0,(-25/146),(-25/559),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;(-1/8),(-1/39),1,0,0,0,0;(-1/8),(-1/39),(-1/38),1,0,0,0;(-1/8),(-1/39),(-1/38),(-1/37),1,0,0;0,0,0,0,(-37/254),1,0;0,0,0,0,(-37/254),(-37/1233),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;(-1/9),(-1/53),1,0,0,0,0;(-1/9),(-1/53),(-1/52),1,0,0,0;(-1/9),(-1/53),(-1/52),(-1/51),1,0,0;0,0,0,0,(-17/134),1,0;0,0,0,0,(-17/134),(-17/787),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;(-1/10),(-1/69),1,0,0,0,0;(-1/10),(-1/69),(-1/68),1,0,0,0;(-1/10),(-1/69),(-1/68),(-1/67),1,0,0;0,0,0,0,(-67/596),1,0;0,0,0,0,(-67/596),(-67/4105),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;(-1/11),(-1/87),1,0,0,0,0;(-1/11),(-1/87),(-1/86),1,0,0,0;(-1/11),(-1/87),(-1/86),(-1/85),1,0,0;0,0,0,0,(-85/842),1,0;0,0,0,0,(-85/842),(-85/6651),1],!![1,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0;(-1/12),(-1/107),1,0,0,0,0;(-1/12),(-1/107),(-1/106),1,0,0,0;(-1/12),(-1/107),(-1/106),(-1/105),1,0,0;0,0,0,0,(-35/382),1,0;0,0,0,0,(-35/382),(-35/3403),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-5,1,1,1,1,0,0;0,(-9/5),(1/5),(1/5),(1/5),0,0;0,0,(-16/9),(2/9),(2/9),0,0;0,0,0,(-7/4),(1/4),0,0;0,0,0,0,(-26/7),1,1;0,0,0,0,0,(-45/26),(7/26);0,0,0,0,0,0,(-76/45)],!![-6,1,1,1,1,0,0;0,(-17/6),(1/6),(1/6),(1/6),0,0;0,0,(-48/17),(3/17),(3/17),0,0;0,0,0,(-45/16),(3/16),0,0;0,0,0,0,(-24/5),1,1;0,0,0,0,0,(-67/24),(5/24);0,0,0,0,0,0,(-186/67)],!![-7,1,1,1,1,0,0;0,(-27/7),(1/7),(1/7),(1/7),0,0;0,0,(-104/27),(4/27),(4/27),0,0;0,0,0,(-50/13),(2/13),0,0;0,0,0,0,(-146/25),1,1;0,0,0,0,0,(-559/146),(25/146);0,0,0,0,0,0,(-2136/559)],!![-8,1,1,1,1,0,0;0,(-39/8),(1/8),(1/8),(1/8),0,0;0,0,(-190/39),(5/39),(5/39),0,0;0,0,0,(-185/38),(5/38),0,0;0,0,0,0,(-254/37),1,1;0,0,0,0,0,(-1233/254),(37/254);0,0,0,0,0,0,(-5980/1233)],!![-9,1,1,1,1,0,0;0,(-53/9),(1/9),(1/9),(1/9),0,0;0,0,(-312/53),(6/53),(6/53),0,0;0,0,0,(-153/26),(3/26),0,0;0,0,0,0,(-134/17),1,1;0,0,0,0,0,(-787/134),(17/134);0,0,0,0,0,0,(-4620/787)],!![-10,1,1,1,1,0,0;0,(-69/10),(1/10),(1/10),(1/10),0,0;0,0,(-476/69),(7/69),(7/69),0,0;0,0,0,(-469/68),(7/68),0,0;0,0,0,0,(-596/67),1,1;0,0,0,0,0,(-4105/596),(67/596);0,0,0,0,0,0,(-28266/4105)],!![-11,1,1,1,1,0,0;0,(-87/11),(1/11),(1/11),(1/11),0,0;0,0,(-688/87),(8/87),(8/87),0,0;0,0,0,(-340/43),(4/43),0,0;0,0,0,0,(-842/85),1,1;0,0,0,0,0,(-6651/842),(85/842);0,0,0,0,0,0,(-52528/6651)],!![-12,1,1,1,1,0,0;0,(-107/12),(1/12),(1/12),(1/12),0,0;0,0,(-954/107),(9/107),(9/107),0,0;0,0,0,(-945/106),(9/106),0,0;0,0,0,0,(-382/35),1,1;0,0,0,0,0,(-3403/382),(35/382);0,0,0,0,0,0,(-30312/3403)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-7,21,-9,1],count := 4,lower := ![(-1/268435456),(53461717/134217728),(448270687/134217728),(353113571/67108864)],upper := ![(7/134217728),(106923449/268435456),(896541389/268435456),(1412454299/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 3}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((4860259331/939524096) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((1215064859/234881024) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum011
