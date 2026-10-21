/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum022
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,true,false,true,false,false],![true,false,true,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,true,false,false,false],![false,false,false,true,false,false,false,false],![true,false,false,false,false,false,true,false],![false,false,false,false,false,true,false,true],![false,false,false,false,false,false,true,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,72,-224,307,-212,77,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/11),1,0,0,0,0,0;(-1/4),(-1/11),(-1/18),1,0,0,0,0;0,0,0,(-18/49),1,0,0,0;(-1/4),(-1/11),(-1/18),(-5/49),(-1/16),1,0,0;0,0,0,0,0,(-16/43),1,0;0,0,0,0,0,0,(-43/113),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/19),1,0,0,0,0,0;(-1/5),(-1/19),(-1/52),1,0,0,0,0;0,0,0,(-52/197),1,0,0,0;(-1/5),(-1/19),(-1/52),(-11/197),(-1/49),1,0,0;0,0,0,0,0,(-49/185),1,0;0,0,0,0,0,0,(-185/691),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/29),1,0,0,0,0,0;(-1/6),(-1/29),(-1/110),1,0,0,0,0;0,0,0,(-110/531),1,0,0,0;(-1/6),(-1/29),(-1/110),(-19/531),(-1/106),1,0,0;0,0,0,0,0,(-106/511),1,0;0,0,0,0,0,0,(-511/2449),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/41),1,0,0,0,0,0;(-1/7),(-1/41),(-1/198),1,0,0,0,0;0,0,0,(-198/1159),1,0,0,0;(-1/7),(-1/41),(-1/198),(-29/1159),(-1/193),1,0,0;0,0,0,0,0,(-193/1129),1,0;0,0,0,0,0,0,(-1129/6581),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/55),1,0,0,0,0,0;(-1/8),(-1/55),(-1/322),1,0,0,0,0;0,0,0,(-322/2213),1,0,0,0;(-1/8),(-1/55),(-1/322),(-41/2213),(-1/316),1,0,0;0,0,0,0,0,(-316/2171),1,0;0,0,0,0,0,0,(-2171/14881),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/71),1,0,0,0,0,0;(-1/9),(-1/71),(-1/488),1,0,0,0,0;0,0,0,(-488/3849),1,0,0,0;(-1/9),(-1/71),(-1/488),(-55/3849),(-1/481),1,0,0;0,0,0,0,0,(-481/3793),1,0;0,0,0,0,0,0,(-3793/29863),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/89),1,0,0,0,0,0;(-1/10),(-1/89),(-1/702),1,0,0,0,0;0,0,0,(-702/6247),1,0,0,0;(-1/10),(-1/89),(-1/702),(-71/6247),(-1/694),1,0,0;0,0,0,0,0,(-694/6175),1,0;0,0,0,0,0,0,(-6175/54881),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/109),1,0,0,0,0,0;(-1/11),(-1/109),(-1/970),1,0,0,0,0;0,0,0,(-970/9611),1,0,0,0;(-1/11),(-1/109),(-1/970),(-89/9611),(-1/961),1,0,0;0,0,0,0,0,(-961/9521),1,0;0,0,0,0,0,0,(-9521/94249),1],!![1,0,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0,0;0,(-12/131),1,0,0,0,0,0;(-1/12),(-1/131),(-1/1298),1,0,0,0,0;0,0,0,(-1298/14169),1,0,0,0;(-1/12),(-1/131),(-1/1298),(-109/14169),(-1/1288),1,0,0;0,0,0,0,0,(-1288/14059),1,0;0,0,0,0,0,0,(-14059/153361),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-4,1,0,1,0,1,0,0;0,(-11/4),1,(1/4),0,(1/4),0,0;0,0,(-18/11),(1/11),0,(1/11),0,0;0,0,0,(-49/18),1,(5/18),0,0;0,0,0,0,(-80/49),(5/49),0,0;0,0,0,0,0,(-43/16),1,0;0,0,0,0,0,0,(-113/43),1;0,0,0,0,0,0,0,(-183/113)],!![-5,1,0,1,0,1,0,0;0,(-19/5),1,(1/5),0,(1/5),0,0;0,0,(-52/19),(1/19),0,(1/19),0,0;0,0,0,(-197/52),1,(11/52),0,0;0,0,0,0,(-539/197),(11/197),0,0;0,0,0,0,0,(-185/49),1,0;0,0,0,0,0,0,(-691/185),1;0,0,0,0,0,0,0,(-1888/691)],!![-6,1,0,1,0,1,0,0;0,(-29/6),1,(1/6),0,(1/6),0,0;0,0,(-110/29),(1/29),0,(1/29),0,0;0,0,0,(-531/110),1,(19/110),0,0;0,0,0,0,(-2014/531),(19/531),0,0;0,0,0,0,0,(-511/106),1,0;0,0,0,0,0,0,(-2449/511),1;0,0,0,0,0,0,0,(-9285/2449)],!![-7,1,0,1,0,1,0,0;0,(-41/7),1,(1/7),0,(1/7),0,0;0,0,(-198/41),(1/41),0,(1/41),0,0;0,0,0,(-1159/198),1,(29/198),0,0;0,0,0,0,(-5597/1159),(29/1159),0,0;0,0,0,0,0,(-1129/193),1,0;0,0,0,0,0,0,(-6581/1129),1;0,0,0,0,0,0,0,(-31776/6581)],!![-8,1,0,1,0,1,0,0;0,(-55/8),1,(1/8),0,(1/8),0,0;0,0,(-322/55),(1/55),0,(1/55),0,0;0,0,0,(-2213/322),1,(41/322),0,0;0,0,0,0,(-12956/2213),(41/2213),0,0;0,0,0,0,0,(-2171/316),1,0;0,0,0,0,0,0,(-14881/2171),1;0,0,0,0,0,0,0,(-87115/14881)],!![-9,1,0,1,0,1,0,0;0,(-71/9),1,(1/9),0,(1/9),0,0;0,0,(-488/71),(1/71),0,(1/71),0,0;0,0,0,(-3849/488),1,(55/488),0,0;0,0,0,0,(-26455/3849),(55/3849),0,0;0,0,0,0,0,(-3793/481),1,0;0,0,0,0,0,0,(-29863/3793),1;0,0,0,0,0,0,0,(-205248/29863)],!![-10,1,0,1,0,1,0,0;0,(-89/10),1,(1/10),0,(1/10),0,0;0,0,(-702/89),(1/89),0,(1/89),0,0;0,0,0,(-6247/702),1,(71/702),0,0;0,0,0,0,(-49274/6247),(71/6247),0,0;0,0,0,0,0,(-6175/694),1,0;0,0,0,0,0,0,(-54881/6175),1;0,0,0,0,0,0,0,(-432873/54881)],!![-11,1,0,1,0,1,0,0;0,(-109/11),1,(1/11),0,(1/11),0,0;0,0,(-970/109),(1/109),0,(1/109),0,0;0,0,0,(-9611/970),1,(89/970),0,0;0,0,0,0,(-85529/9611),(89/9611),0,0;0,0,0,0,0,(-9521/961),1,0;0,0,0,0,0,0,(-94249/9521),1;0,0,0,0,0,0,0,(-838720/94249)],!![-12,1,0,1,0,1,0,0;0,(-131/12),1,(1/12),0,(1/12),0,0;0,0,(-1298/131),(1/131),0,(1/131),0,0;0,0,0,(-14169/1298),1,(109/1298),0,0;0,0,0,0,(-140392/14169),(109/14169),0,0;0,0,0,0,0,(-14059/1288),1,0;0,0,0,0,0,0,(-153361/14059),1;0,0,0,0,0,0,0,(-1519551/153361)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,72,-224,307,-212,77,-14,1],count := 8,lower := ![(-15/536870912),(130675313/536870912),(205066429/536870912),(633373847/536870912),(1073741813/536870912),(1405546283/536870912),(1685003843/536870912),(2382785163/536870912)],upper := ![(1/268435456),(65337665/268435456),(102533223/268435456),(79171733/67108864),(536870915/268435456),(351386575/134217728),(421250965/134217728),(595696295/134217728)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((1394490359/268435456) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((1394490393/268435456) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum022
