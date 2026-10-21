/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum010
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,false,true,false,false],![true,false,true,false,false,false,false],![false,true,false,true,false,false,false],![false,false,true,false,false,false,false],![true,false,false,false,false,true,false],![false,false,false,false,true,false,true],![false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-56,126,-120,55,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0;0,(-3/8),1,0,0,0,0;0,0,(-8/21),1,0,0,0;(-1/3),(-1/8),(-1/21),(-1/34),1,0,0;0,0,0,0,(-34/89),1,0;0,0,0,0,0,(-89/233),1],!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/15),1,0,0,0,0;0,0,(-15/56),1,0,0,0;(-1/4),(-1/15),(-1/56),(-1/153),1,0,0;0,0,0,0,(-153/571),1,0;0,0,0,0,0,(-571/2131),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/24),1,0,0,0,0;0,0,(-24/115),1,0,0,0;(-1/5),(-1/24),(-1/115),(-1/436),1,0,0;0,0,0,0,(-436/2089),1,0;0,0,0,0,0,(-2089/10009),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/35),1,0,0,0,0;0,0,(-35/204),1,0,0,0;(-1/6),(-1/35),(-1/204),(-1/985),1,0,0;0,0,0,0,(-985/5741),1,0;0,0,0,0,0,(-5741/33461),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/48),1,0,0,0,0;0,0,(-48/329),1,0,0,0;(-1/7),(-1/48),(-1/329),(-1/1926),1,0,0;0,0,0,0,(-1926/13201),1,0;0,0,0,0,0,(-13201/90481),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/63),1,0,0,0,0;0,0,(-63/496),1,0,0,0;(-1/8),(-1/63),(-1/496),(-1/3409),1,0,0;0,0,0,0,(-3409/26839),1,0;0,0,0,0,0,(-26839/211303),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/80),1,0,0,0,0;0,0,(-80/711),1,0,0,0;(-1/9),(-1/80),(-1/711),(-1/5608),1,0,0;0,0,0,0,(-5608/49841),1,0;0,0,0,0,0,(-49841/442961),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/99),1,0,0,0,0;0,0,(-99/980),1,0,0,0;(-1/10),(-1/99),(-1/980),(-1/8721),1,0,0;0,0,0,0,(-8721/86329),1,0;0,0,0,0,0,(-86329/854569),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-3,1,0,0,1,0,0;0,(-8/3),1,0,(1/3),0,0;0,0,(-21/8),1,(1/8),0,0;0,0,0,(-34/21),(1/21),0,0;0,0,0,0,(-89/34),1,0;0,0,0,0,0,(-233/89),1;0,0,0,0,0,0,(-377/233)],!![-4,1,0,0,1,0,0;0,(-15/4),1,0,(1/4),0,0;0,0,(-56/15),1,(1/15),0,0;0,0,0,(-153/56),(1/56),0,0;0,0,0,0,(-571/153),1,0;0,0,0,0,0,(-2131/571),1;0,0,0,0,0,0,(-5822/2131)],!![-5,1,0,0,1,0,0;0,(-24/5),1,0,(1/5),0,0;0,0,(-115/24),1,(1/24),0,0;0,0,0,(-436/115),(1/115),0,0;0,0,0,0,(-2089/436),1,0;0,0,0,0,0,(-10009/2089),1;0,0,0,0,0,0,(-37947/10009)],!![-6,1,0,0,1,0,0;0,(-35/6),1,0,(1/6),0,0;0,0,(-204/35),1,(1/35),0,0;0,0,0,(-985/204),(1/204),0,0;0,0,0,0,(-5741/985),1,0;0,0,0,0,0,(-33461/5741),1;0,0,0,0,0,0,(-161564/33461)],!![-7,1,0,0,1,0,0;0,(-48/7),1,0,(1/7),0,0;0,0,(-329/48),1,(1/48),0,0;0,0,0,(-1926/329),(1/329),0,0;0,0,0,0,(-13201/1926),1,0;0,0,0,0,0,(-90481/13201),1;0,0,0,0,0,0,(-529685/90481)],!![-8,1,0,0,1,0,0;0,(-63/8),1,0,(1/8),0,0;0,0,(-496/63),1,(1/63),0,0;0,0,0,(-3409/496),(1/496),0,0;0,0,0,0,(-26839/3409),1,0;0,0,0,0,0,(-211303/26839),1;0,0,0,0,0,0,(-1452282/211303)],!![-9,1,0,0,1,0,0;0,(-80/9),1,0,(1/9),0,0;0,0,(-711/80),1,(1/80),0,0;0,0,0,(-5608/711),(1/711),0,0;0,0,0,0,(-49841/5608),1,0;0,0,0,0,0,(-442961/49841),1;0,0,0,0,0,0,(-3493847/442961)],!![-10,1,0,0,1,0,0;0,(-99/10),1,0,(1/10),0,0;0,0,(-980/99),1,(1/99),0,0;0,0,0,(-8721/980),(1/980),0,0;0,0,0,0,(-86329/8721),1,0;0,0,0,0,0,(-854569/86329),1;0,0,0,0,0,0,(-7604792/854569)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-56,126,-120,55,-12,1],count := 7,lower := ![(-1/268435456),(53166929/268435456),(202137359/268435456),(104351471/67108864),(656335919/268435456),(217901111/67108864),(1020574889/268435456)],upper := ![(7/134217728),(1661467/8388608),(101068687/134217728),(417405899/268435456),(328167967/134217728),(871604459/268435456),(127571863/33554432)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((2043982587/469762048) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((8175930663/1879048192) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum010
