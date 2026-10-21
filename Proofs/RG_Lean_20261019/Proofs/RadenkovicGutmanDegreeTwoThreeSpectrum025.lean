/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
import Proofs.RadenkovicGutmanRationalSpectralBounds
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum025
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,true,true,true,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,false,false,false],![true,false,false,false,false,true,true,true],![false,false,false,false,true,false,false,false],![false,false,false,false,true,false,false,false],![false,false,false,false,true,false,false,false]]
def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,-8,58,-162,229,-176,72,-14,1]
def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;(-1/5),(-1/9),1,0,0,0,0,0;(-1/5),(-1/9),(-1/8),1,0,0,0,0;(-1/5),(-1/9),(-1/8),(-1/7),1,0,0,0;0,0,0,0,(-7/33),1,0,0;0,0,0,0,(-7/33),(-7/59),1,0;0,0,0,0,(-7/33),(-7/59),(-7/52),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;(-1/6),(-1/17),1,0,0,0,0,0;(-1/6),(-1/17),(-1/16),1,0,0,0,0;(-1/6),(-1/17),(-1/16),(-1/15),1,0,0,0;0,0,0,0,(-5/29),1,0,0;0,0,0,0,(-5/29),(-5/82),1,0;0,0,0,0,(-5/29),(-5/82),(-5/77),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;(-1/7),(-1/27),1,0,0,0,0,0;(-1/7),(-1/27),(-1/26),1,0,0,0,0;(-1/7),(-1/27),(-1/26),(-1/25),1,0,0,0;0,0,0,0,(-25/171),1,0,0;0,0,0,0,(-25/171),(-25/659),1,0;0,0,0,0,(-25/171),(-25/659),(-25/634),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;(-1/8),(-1/39),1,0,0,0,0,0;(-1/8),(-1/39),(-1/38),1,0,0,0,0;(-1/8),(-1/39),(-1/38),(-1/37),1,0,0,0;0,0,0,0,(-37/291),1,0,0;0,0,0,0,(-37/291),(-37/1418),1,0;0,0,0,0,(-37/291),(-37/1418),(-37/1381),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;(-1/9),(-1/53),1,0,0,0,0,0;(-1/9),(-1/53),(-1/52),1,0,0,0,0;(-1/9),(-1/53),(-1/52),(-1/51),1,0,0,0;0,0,0,0,(-17/151),1,0,0;0,0,0,0,(-17/151),(-17/889),1,0;0,0,0,0,(-17/151),(-17/889),(-17/872),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;(-1/10),(-1/69),1,0,0,0,0,0;(-1/10),(-1/69),(-1/68),1,0,0,0,0;(-1/10),(-1/69),(-1/68),(-1/67),1,0,0,0;0,0,0,0,(-67/663),1,0,0;0,0,0,0,(-67/663),(-67/4574),1,0;0,0,0,0,(-67/663),(-67/4574),(-67/4507),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;(-1/11),(-1/87),1,0,0,0,0,0;(-1/11),(-1/87),(-1/86),1,0,0,0,0;(-1/11),(-1/87),(-1/86),(-1/85),1,0,0,0;0,0,0,0,(-85/927),1,0,0;0,0,0,0,(-85/927),(-85/7331),1,0;0,0,0,0,(-85/927),(-85/7331),(-85/7246),1],!![1,0,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0,0;(-1/12),(-1/107),1,0,0,0,0,0;(-1/12),(-1/107),(-1/106),1,0,0,0,0;(-1/12),(-1/107),(-1/106),(-1/105),1,0,0,0;0,0,0,0,(-35/417),1,0,0;0,0,0,0,(-35/417),(-35/3718),1,0;0,0,0,0,(-35/417),(-35/3718),(-35/3683),1],!![1,0,0,0,0,0,0,0;(-1/13),1,0,0,0,0,0,0;(-1/13),(-1/129),1,0,0,0,0,0;(-1/13),(-1/129),(-1/128),1,0,0,0,0;(-1/13),(-1/129),(-1/128),(-1/127),1,0,0,0;0,0,0,0,(-127/1641),1,0,0;0,0,0,0,(-127/1641),(-127/16283),1,0;0,0,0,0,(-127/1641),(-127/16283),(-127/16156),1]]
def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-5,1,1,1,1,0,0,0;0,(-9/5),(1/5),(1/5),(1/5),0,0,0;0,0,(-16/9),(2/9),(2/9),0,0,0;0,0,0,(-7/4),(1/4),0,0,0;0,0,0,0,(-33/7),1,1,1;0,0,0,0,0,(-59/33),(7/33),(7/33);0,0,0,0,0,0,(-104/59),(14/59);0,0,0,0,0,0,0,(-45/26)],!![-6,1,1,1,1,0,0,0;0,(-17/6),(1/6),(1/6),(1/6),0,0,0;0,0,(-48/17),(3/17),(3/17),0,0,0;0,0,0,(-45/16),(3/16),0,0,0;0,0,0,0,(-29/5),1,1,1;0,0,0,0,0,(-82/29),(5/29),(5/29);0,0,0,0,0,0,(-231/82),(15/82);0,0,0,0,0,0,0,(-216/77)],!![-7,1,1,1,1,0,0,0;0,(-27/7),(1/7),(1/7),(1/7),0,0,0;0,0,(-104/27),(4/27),(4/27),0,0,0;0,0,0,(-50/13),(2/13),0,0,0;0,0,0,0,(-171/25),1,1,1;0,0,0,0,0,(-659/171),(25/171),(25/171);0,0,0,0,0,0,(-2536/659),(100/659);0,0,0,0,0,0,0,(-1218/317)],!![-8,1,1,1,1,0,0,0;0,(-39/8),(1/8),(1/8),(1/8),0,0,0;0,0,(-190/39),(5/39),(5/39),0,0,0;0,0,0,(-185/38),(5/38),0,0,0;0,0,0,0,(-291/37),1,1,1;0,0,0,0,0,(-1418/291),(37/291),(37/291);0,0,0,0,0,0,(-6905/1418),(185/1418);0,0,0,0,0,0,0,(-6720/1381)],!![-9,1,1,1,1,0,0,0;0,(-53/9),(1/9),(1/9),(1/9),0,0,0;0,0,(-312/53),(6/53),(6/53),0,0,0;0,0,0,(-153/26),(3/26),0,0,0;0,0,0,0,(-151/17),1,1,1;0,0,0,0,0,(-889/151),(17/151),(17/151);0,0,0,0,0,0,(-5232/889),(102/889);0,0,0,0,0,0,0,(-2565/436)],!![-10,1,1,1,1,0,0,0;0,(-69/10),(1/10),(1/10),(1/10),0,0,0;0,0,(-476/69),(7/69),(7/69),0,0,0;0,0,0,(-469/68),(7/68),0,0,0;0,0,0,0,(-663/67),1,1,1;0,0,0,0,0,(-4574/663),(67/663),(67/663);0,0,0,0,0,0,(-31549/4574),(469/4574);0,0,0,0,0,0,0,(-31080/4507)],!![-11,1,1,1,1,0,0,0;0,(-87/11),(1/11),(1/11),(1/11),0,0,0;0,0,(-688/87),(8/87),(8/87),0,0,0;0,0,0,(-340/43),(4/43),0,0,0;0,0,0,0,(-927/85),1,1,1;0,0,0,0,0,(-7331/927),(85/927),(85/927);0,0,0,0,0,0,(-57968/7331),(680/7331);0,0,0,0,0,0,0,(-28644/3623)],!![-12,1,1,1,1,0,0,0;0,(-107/12),(1/12),(1/12),(1/12),0,0,0;0,0,(-954/107),(9/107),(9/107),0,0,0;0,0,0,(-945/106),(9/106),0,0,0;0,0,0,0,(-417/35),1,1,1;0,0,0,0,0,(-3718/417),(35/417),(35/417);0,0,0,0,0,0,(-33147/3718),(315/3718);0,0,0,0,0,0,0,(-32832/3683)],!![-13,1,1,1,1,0,0,0;0,(-129/13),(1/13),(1/13),(1/13),0,0,0;0,0,(-1280/129),(10/129),(10/129),0,0,0;0,0,0,(-635/64),(5/64),0,0,0;0,0,0,0,(-1641/127),1,1,1;0,0,0,0,0,(-16283/1641),(127/1641),(127/1641);0,0,0,0,0,0,(-161560/16283),(1270/16283);0,0,0,0,0,0,0,(-80145/8078)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-8,26,-10,1],count := 4,lower := ![(-15/536870912),(95092901/268435456),(2147483641/536870912),(757759913/134217728)],upper := ![(1/268435456),(190185819/536870912),(1073741829/268435456),(3031039669/536870912)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(536870899/536870912)],upper := ![(134217729/134217728)],copies := 4}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((3299475101/536870912) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((3299475135/536870912) : ℝ) := by
  have hi : graphDecidable=
      (fun i j => Classical.propDecidable (graph.Adj i j)) := Subsingleton.elim _ _
  have hp := graph_charpoly.trans factorization
  rw [hi] at hp ⊢
  have h := RationalSpectralBounds.graph_bounds graph boxes boxes_accepted hp
    (2-2/8) (3299475101/536870912) (3299475135/536870912) (by decide +kernel)
  norm_num at h ⊢
  exact h
#print axioms matrix_certificates
#print axioms graph_charpoly
#print axioms boxes_accepted
#print axioms factorization
#print axioms actual_graph_bounds
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeSpectrum025
