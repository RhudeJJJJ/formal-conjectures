/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum013
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,false,true,false,false],![true,false,true,true,false,false,false],![false,true,false,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,false,true,true],![false,false,false,false,true,false,false],![false,false,false,false,true,false,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-48,107,-108,53,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0;0,(-3/11),1,0,0,0,0;0,(-3/11),(-3/19),1,0,0,0;(-1/3),(-1/11),(-1/19),(-1/16),1,0,0;0,0,0,0,(-8/29),1,0;0,0,0,0,(-8/29),(-4/25),1],!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/19),1,0,0,0,0;0,(-4/19),(-4/53),1,0,0,0;(-1/4),(-1/19),(-1/53),(-1/49),1,0,0;0,0,0,0,(-49/232),1,0;0,0,0,0,(-49/232),(-49/647),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/29),1,0,0,0,0;0,(-5/29),(-5/111),1,0,0,0;(-1/5),(-1/29),(-1/111),(-1/106),1,0,0;0,0,0,0,(-53/307),1,0;0,0,0,0,(-53/307),(-53/1175),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/41),1,0,0,0,0;0,(-6/41),(-6/199),1,0,0,0;(-1/6),(-1/41),(-1/199),(-1/193),1,0,0;0,0,0,0,(-193/1318),1,0;0,0,0,0,(-193/1318),(-193/6397),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/55),1,0,0,0,0;0,(-7/55),(-7/323),1,0,0,0;(-1/7),(-1/55),(-1/323),(-1/316),1,0,0;0,0,0,0,(-158/1241),1,0;0,0,0,0,(-158/1241),(-79/3644),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/71),1,0,0,0,0;0,(-8/71),(-8/489),1,0,0,0;(-1/8),(-1/71),(-1/489),(-1/481),1,0,0;0,0,0,0,(-481/4268),1,0;0,0,0,0,(-481/4268),(-481/29395),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/89),1,0,0,0,0;0,(-9/89),(-9/703),1,0,0,0;(-1/9),(-1/89),(-1/703),(-1/694),1,0,0;0,0,0,0,(-347/3431),1,0;0,0,0,0,(-347/3431),(-347/27101),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/109),1,0,0,0,0;0,(-10/109),(-10/971),1,0,0,0;(-1/10),(-1/109),(-1/971),(-1/961),1,0,0;0,0,0,0,(-961/10474),1,0;0,0,0,0,(-961/10474),(-961/93305),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-3,1,0,0,1,0,0;0,(-11/3),1,1,(1/3),0,0;0,0,(-19/11),(3/11),(1/11),0,0;0,0,0,(-32/19),(2/19),0,0;0,0,0,0,(-29/8),1,1;0,0,0,0,0,(-50/29),(8/29);0,0,0,0,0,0,(-42/25)],!![-4,1,0,0,1,0,0;0,(-19/4),1,1,(1/4),0,0;0,0,(-53/19),(4/19),(1/19),0,0;0,0,0,(-147/53),(3/53),0,0;0,0,0,0,(-232/49),1,1;0,0,0,0,0,(-647/232),(49/232);0,0,0,0,0,0,(-1794/647)],!![-5,1,0,0,1,0,0;0,(-29/5),1,1,(1/5),0,0;0,0,(-111/29),(5/29),(1/29),0,0;0,0,0,(-424/111),(4/111),0,0;0,0,0,0,(-307/53),1,1;0,0,0,0,0,(-1175/307),(53/307);0,0,0,0,0,0,(-4488/1175)],!![-6,1,0,0,1,0,0;0,(-41/6),1,1,(1/6),0,0;0,0,(-199/41),(6/41),(1/41),0,0;0,0,0,(-965/199),(5/199),0,0;0,0,0,0,(-1318/193),1,1;0,0,0,0,0,(-6397/1318),(193/1318);0,0,0,0,0,0,(-31020/6397)],!![-7,1,0,0,1,0,0;0,(-55/7),1,1,(1/7),0,0;0,0,(-323/55),(7/55),(1/55),0,0;0,0,0,(-1896/323),(6/323),0,0;0,0,0,0,(-1241/158),1,1;0,0,0,0,0,(-7288/1241),(158/1241);0,0,0,0,0,0,(-10695/1822)],!![-8,1,0,0,1,0,0;0,(-71/8),1,1,(1/8),0,0;0,0,(-489/71),(8/71),(1/71),0,0;0,0,0,(-3367/489),(7/489),0,0;0,0,0,0,(-4268/481),1,1;0,0,0,0,0,(-29395/4268),(481/4268);0,0,0,0,0,0,(-202398/29395)],!![-9,1,0,0,1,0,0;0,(-89/9),1,1,(1/9),0,0;0,0,(-703/89),(9/89),(1/89),0,0;0,0,0,(-5552/703),(8/703),0,0;0,0,0,0,(-3431/347),1,1;0,0,0,0,0,(-27101/3431),(347/3431);0,0,0,0,0,0,(-214032/27101)],!![-10,1,0,0,1,0,0;0,(-109/10),1,1,(1/10),0,0;0,0,(-971/109),(10/109),(1/109),0,0;0,0,0,(-8649/971),(9/971),0,0;0,0,0,0,(-10474/961),1,1;0,0,0,0,0,(-93305/10474),(961/10474);0,0,0,0,0,0,(-831096/93305)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-34,32,-10,1],count := 5,lower := ![(-1/268435456),(35963527/134217728),(212840647/134217728),(1001814749/268435456),(1184931419/268435456)],upper := ![(7/134217728),(71927069/268435456),(425681309/268435456),(250453691/67108864),(592465717/134217728)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 2}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((1108096529/234881024) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((4432386221/939524096) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum013
