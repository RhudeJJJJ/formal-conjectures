/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum021
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,false,true,false,false],![true,false,true,false,false,false,false,false],![false,true,false,true,true,false,false,false],![false,false,true,false,false,false,false,false],![false,false,true,false,false,false,false,false],![true,false,false,false,false,false,true,false],![false,false,false,false,false,true,false,true],![false,false,false,false,false,false,true,false]]
noncomputable def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,-8,79,-232,309,-212,77,-14,1]
noncomputable def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/8),1,0,0,0,0,0;0,0,(-8/29),1,0,0,0,0;0,0,(-8/29),(-4/25),1,0,0,0;(-1/3),(-1/8),(-1/29),(-1/50),(-1/42),1,0,0;0,0,0,0,0,(-21/55),1,0;0,0,0,0,0,0,(-55/144),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/15),1,0,0,0,0,0;0,0,(-15/71),1,0,0,0,0;0,0,(-15/71),(-5/66),1,0,0,0;(-1/4),(-1/15),(-1/71),(-1/198),(-1/183),1,0,0;0,0,0,0,0,(-183/683),1,0;0,0,0,0,0,0,(-683/2549),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/24),1,0,0,0,0,0;0,0,(-24/139),1,0,0,0,0;0,0,(-24/139),(-6/133),1,0,0,0;(-1/5),(-1/24),(-1/139),(-1/532),(-1/508),1,0,0;0,0,0,0,0,(-254/1217),1,0;0,0,0,0,0,0,(-1217/5831),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/35),1,0,0,0,0,0;0,0,(-35/239),1,0,0,0,0;0,0,(-35/239),(-7/232),1,0,0,0;(-1/6),(-1/35),(-1/239),(-1/1160),(-1/1125),1,0,0;0,0,0,0,0,(-1125/6557),1,0;0,0,0,0,0,0,(-6557/38217),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/48),1,0,0,0,0,0;0,0,(-48/377),1,0,0,0,0;0,0,(-48/377),(-8/369),1,0,0,0;(-1/7),(-1/48),(-1/377),(-1/2214),(-1/2166),1,0,0;0,0,0,0,0,(-1083/7423),1,0;0,0,0,0,0,0,(-7423/50878),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/63),1,0,0,0,0,0;0,0,(-63/559),1,0,0,0,0;0,0,(-63/559),(-9/550),1,0,0,0;(-1/8),(-1/63),(-1/559),(-1/3850),(-1/3787),1,0,0;0,0,0,0,0,(-3787/29815),1,0;0,0,0,0,0,0,(-29815/234733),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/80),1,0,0,0,0,0;0,0,(-80/791),1,0,0,0,0;0,0,(-80/791),(-10/781),1,0,0,0;(-1/9),(-1/80),(-1/791),(-1/6248),(-1/6168),1,0,0;0,0,0,0,0,(-3084/27409),1,0;0,0,0,0,0,0,(-27409/243597),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/99),1,0,0,0,0,0;0,0,(-99/1079),1,0,0,0,0;0,0,(-99/1079),(-11/1068),1,0,0,0;(-1/10),(-1/99),(-1/1079),(-1/9612),(-1/9513),1,0,0;0,0,0,0,0,(-9513/94169),1,0;0,0,0,0,0,0,(-94169/932177),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/120),1,0,0,0,0,0;0,0,(-120/1429),1,0,0,0,0;0,0,(-120/1429),(-12/1417),1,0,0,0;(-1/11),(-1/120),(-1/1429),(-1/14170),(-1/14050),1,0,0;0,0,0,0,0,(-7025/76631),1,0;0,0,0,0,0,0,(-76631/835916),1]]
noncomputable def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,0,1,0,0;0,(-8/3),1,0,0,(1/3),0,0;0,0,(-29/8),1,1,(1/8),0,0;0,0,0,(-50/29),(8/29),(1/29),0,0;0,0,0,0,(-42/25),(1/25),0,0;0,0,0,0,0,(-55/21),1,0;0,0,0,0,0,0,(-144/55),1;0,0,0,0,0,0,0,(-233/144)],!![-4,1,0,0,0,1,0,0;0,(-15/4),1,0,0,(1/4),0,0;0,0,(-71/15),1,1,(1/15),0,0;0,0,0,(-198/71),(15/71),(1/71),0,0;0,0,0,0,(-61/22),(1/66),0,0;0,0,0,0,0,(-683/183),1,0;0,0,0,0,0,0,(-2549/683),1;0,0,0,0,0,0,0,(-6964/2549)],!![-5,1,0,0,0,1,0,0;0,(-24/5),1,0,0,(1/5),0,0;0,0,(-139/24),1,1,(1/24),0,0;0,0,0,(-532/139),(24/139),(1/139),0,0;0,0,0,0,(-508/133),(1/133),0,0;0,0,0,0,0,(-1217/254),1,0;0,0,0,0,0,0,(-5831/1217),1;0,0,0,0,0,0,0,(-22107/5831)],!![-6,1,0,0,0,1,0,0;0,(-35/6),1,0,0,(1/6),0,0;0,0,(-239/35),1,1,(1/35),0,0;0,0,0,(-1160/239),(35/239),(1/239),0,0;0,0,0,0,(-1125/232),(1/232),0,0;0,0,0,0,0,(-6557/1125),1,0;0,0,0,0,0,0,(-38217/6557),1;0,0,0,0,0,0,0,(-184528/38217)],!![-7,1,0,0,0,1,0,0;0,(-48/7),1,0,0,(1/7),0,0;0,0,(-377/48),1,1,(1/48),0,0;0,0,0,(-2214/377),(48/377),(1/377),0,0;0,0,0,0,(-722/123),(1/369),0,0;0,0,0,0,0,(-7423/1083),1,0;0,0,0,0,0,0,(-50878/7423),1;0,0,0,0,0,0,0,(-297845/50878)],!![-8,1,0,0,0,1,0,0;0,(-63/8),1,0,0,(1/8),0,0;0,0,(-559/63),1,1,(1/63),0,0;0,0,0,(-3850/559),(63/559),(1/559),0,0;0,0,0,0,(-3787/550),(1/550),0,0;0,0,0,0,0,(-29815/3787),1,0;0,0,0,0,0,0,(-234733/29815),1;0,0,0,0,0,0,0,(-1613316/234733)],!![-9,1,0,0,0,1,0,0;0,(-80/9),1,0,0,(1/9),0,0;0,0,(-791/80),1,1,(1/80),0,0;0,0,0,(-6248/791),(80/791),(1/791),0,0;0,0,0,0,(-6168/781),(1/781),0,0;0,0,0,0,0,(-27409/3084),1,0;0,0,0,0,0,0,(-243597/27409),1;0,0,0,0,0,0,0,(-1921367/243597)],!![-10,1,0,0,0,1,0,0;0,(-99/10),1,0,0,(1/10),0,0;0,0,(-1079/99),1,1,(1/99),0,0;0,0,0,(-9612/1079),(99/1079),(1/1079),0,0;0,0,0,0,(-3171/356),(1/1068),0,0;0,0,0,0,0,(-94169/9513),1,0;0,0,0,0,0,0,(-932177/94169),1;0,0,0,0,0,0,0,(-8295424/932177)],!![-11,1,0,0,0,1,0,0;0,(-120/11),1,0,0,(1/11),0,0;0,0,(-1429/120),1,1,(1/120),0,0;0,0,0,(-14170/1429),(120/1429),(1/1429),0,0;0,0,0,0,(-14050/1417),(1/1417),0,0;0,0,0,0,0,(-76631/7025),1,0;0,0,0,0,0,0,(-835916/76631),1;0,0,0,0,0,0,0,(-8282529/835916)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,79,-232,309,-212,77,-14,1],count := 8,lower := ![(-15/536870912),(11188189/67108864),(97656951/134217728),(536870899/536870912),(219482113/134217728),(1435007759/536870912),(956782611/268435456),(568171765/134217728)],upper := ![(1/268435456),(89505529/536870912),(390627821/536870912),(134217729/134217728),(877928469/536870912),(44843993/16777216),(1913565239/536870912),(2272687077/536870912)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((2802687753/536870912) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((700671951/134217728) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum021
