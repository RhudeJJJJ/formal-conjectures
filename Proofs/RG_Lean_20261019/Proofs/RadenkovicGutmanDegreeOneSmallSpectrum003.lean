/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum003
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 5 → Fin 5 → Bool := ![![false,true,false,true,false],![true,false,true,false,false],![false,true,false,false,false],![true,false,false,false,true],![false,false,false,true,false]]
def graph : SimpleGraph (Fin 5) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,5,-20,21,-8,1]
def lowerMatrices : Fin 6 → Matrix (Fin 5) (Fin 5) ℚ := ![!![1,0,0,0,0;(-1/3),1,0,0,0;0,(-3/8),1,0,0;(-1/3),(-1/8),(-1/13),1,0;0,0,0,(-13/34),1],!![1,0,0,0,0;(-1/4),1,0,0,0;0,(-4/15),1,0,0;(-1/4),(-1/15),(-1/41),1,0;0,0,0,(-41/153),1],!![1,0,0,0,0;(-1/5),1,0,0,0;0,(-5/24),1,0,0;(-1/5),(-1/24),(-1/91),1,0;0,0,0,(-91/436),1],!![1,0,0,0,0;(-1/6),1,0,0,0;0,(-6/35),1,0,0;(-1/6),(-1/35),(-1/169),1,0;0,0,0,(-169/985),1],!![1,0,0,0,0;(-1/7),1,0,0,0;0,(-7/48),1,0,0;(-1/7),(-1/48),(-1/281),1,0;0,0,0,(-281/1926),1],!![1,0,0,0,0;(-1/8),1,0,0,0;0,(-8/63),1,0,0;(-1/8),(-1/63),(-1/433),1,0;0,0,0,(-433/3409),1]]
def upperMatrices : Fin 6 → Matrix (Fin 5) (Fin 5) ℚ := ![!![-3,1,0,1,0;0,(-8/3),1,(1/3),0;0,0,(-13/8),(1/8),0;0,0,0,(-34/13),1;0,0,0,0,(-55/34)],!![-4,1,0,1,0;0,(-15/4),1,(1/4),0;0,0,(-41/15),(1/15),0;0,0,0,(-153/41),1;0,0,0,0,(-418/153)],!![-5,1,0,1,0;0,(-24/5),1,(1/5),0;0,0,(-91/24),(1/24),0;0,0,0,(-436/91),1;0,0,0,0,(-1653/436)],!![-6,1,0,1,0;0,(-35/6),1,(1/6),0;0,0,(-169/35),(1/35),0;0,0,0,(-985/169),1;0,0,0,0,(-4756/985)],!![-7,1,0,1,0;0,(-48/7),1,(1/7),0;0,0,(-281/48),(1/48),0;0,0,0,(-1926/281),1;0,0,0,0,(-11275/1926)],!![-8,1,0,1,0;0,(-63/8),1,(1/8),0;0,0,(-433/63),(1/63),0;0,0,0,(-3409/433),1;0,0,0,0,(-23430/3409)]]
theorem matrix_certificates : ∀ k : Fin 6,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,5,-20,21,-8,1],count := 5,lower := ![(-3/268435456),(102533219/268435456),(11592771/8388608),(702773145/268435456),(485604299/134217728)],upper := ![(1/33554432),(51266615/134217728),(370968683/268435456),(175693289/67108864),(971208609/268435456)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((4074941419/1342177280) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/5) ∧
    stopLoss (laplacianSpectrum graph) (2-2/5) ≤ ((4074941529/1342177280) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := FactoredRoots.graph_stopLoss_bounds graph boxes boxes_accepted hp (2-2/5)
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum003
