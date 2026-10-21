/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum004
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 6 → Fin 6 → Bool := ![![false,true,false,true,false,false],![true,false,true,false,false,false],![false,true,false,false,false,false],![true,false,false,false,true,false],![false,false,false,true,false,true],![false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 6) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-6,35,-56,36,-10,1]
def lowerMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![1,0,0,0,0,0;(-1/3),1,0,0,0,0;0,(-3/8),1,0,0,0;(-1/3),(-1/8),(-1/13),1,0,0;0,0,0,(-13/34),1,0;0,0,0,0,(-34/89),1],!![1,0,0,0,0,0;(-1/4),1,0,0,0,0;0,(-4/15),1,0,0,0;(-1/4),(-1/15),(-1/41),1,0,0;0,0,0,(-41/153),1,0;0,0,0,0,(-153/571),1],!![1,0,0,0,0,0;(-1/5),1,0,0,0,0;0,(-5/24),1,0,0,0;(-1/5),(-1/24),(-1/91),1,0,0;0,0,0,(-91/436),1,0;0,0,0,0,(-436/2089),1],!![1,0,0,0,0,0;(-1/6),1,0,0,0,0;0,(-6/35),1,0,0,0;(-1/6),(-1/35),(-1/169),1,0,0;0,0,0,(-169/985),1,0;0,0,0,0,(-985/5741),1],!![1,0,0,0,0,0;(-1/7),1,0,0,0,0;0,(-7/48),1,0,0,0;(-1/7),(-1/48),(-1/281),1,0,0;0,0,0,(-281/1926),1,0;0,0,0,0,(-1926/13201),1],!![1,0,0,0,0,0;(-1/8),1,0,0,0,0;0,(-8/63),1,0,0,0;(-1/8),(-1/63),(-1/433),1,0,0;0,0,0,(-433/3409),1,0;0,0,0,0,(-3409/26839),1],!![1,0,0,0,0,0;(-1/9),1,0,0,0,0;0,(-9/80),1,0,0,0;(-1/9),(-1/80),(-1/631),1,0,0;0,0,0,(-631/5608),1,0;0,0,0,0,(-5608/49841),1]]
def upperMatrices : Fin 7 → Matrix (Fin 6) (Fin 6) ℚ := ![!![-3,1,0,1,0,0;0,(-8/3),1,(1/3),0,0;0,0,(-13/8),(1/8),0,0;0,0,0,(-34/13),1,0;0,0,0,0,(-89/34),1;0,0,0,0,0,(-144/89)],!![-4,1,0,1,0,0;0,(-15/4),1,(1/4),0,0;0,0,(-41/15),(1/15),0,0;0,0,0,(-153/41),1,0;0,0,0,0,(-571/153),1;0,0,0,0,0,(-1560/571)],!![-5,1,0,1,0,0;0,(-24/5),1,(1/5),0,0;0,0,(-91/24),(1/24),0,0;0,0,0,(-436/91),1,0;0,0,0,0,(-2089/436),1;0,0,0,0,0,(-7920/2089)],!![-6,1,0,1,0,0;0,(-35/6),1,(1/6),0,0;0,0,(-169/35),(1/35),0,0;0,0,0,(-985/169),1,0;0,0,0,0,(-5741/985),1;0,0,0,0,0,(-27720/5741)],!![-7,1,0,1,0,0;0,(-48/7),1,(1/7),0,0;0,0,(-281/48),(1/48),0,0;0,0,0,(-1926/281),1,0;0,0,0,0,(-13201/1926),1;0,0,0,0,0,(-77280/13201)],!![-8,1,0,1,0,0;0,(-63/8),1,(1/8),0,0;0,0,(-433/63),(1/63),0,0;0,0,0,(-3409/433),1,0;0,0,0,0,(-26839/3409),1;0,0,0,0,0,(-184464/26839)],!![-9,1,0,1,0,0;0,(-80/9),1,(1/9),0,0;0,0,(-631/80),(1/80),0,0;0,0,0,(-5608/631),1,0;0,0,0,0,(-49841/5608),1;0,0,0,0,0,(-393120/49841)]]
theorem matrix_certificates : ∀ k : Fin 7,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-6,35,-56,36,-10,1],count := 6,lower := ![(-3/268435456),(17981765/67108864),(134217725/134217728),(536870903/268435456),(201326589/67108864),(1001814759/268435456)],upper := ![(5/134217728),(71927073/268435456),(268435463/268435456),(134217729/67108864),(805306369/268435456),(250453693/67108864)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((500907369/134217728) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/6) ∧
    stopLoss (laplacianSpectrum graph) (2-2/6) ≤ ((1001814777/268435456) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/6)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum004
