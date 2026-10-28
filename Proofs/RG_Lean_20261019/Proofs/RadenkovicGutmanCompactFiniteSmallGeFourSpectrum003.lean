/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum003
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
noncomputable def adjacency : Fin 8 → Fin 8 → Bool := ![![false,true,false,false,false,false,true,false],![true,false,true,true,true,true,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![false,true,false,false,false,false,false,false],![true,false,false,false,false,false,false,true],![false,false,false,false,false,false,true,false]]
noncomputable def graph : SimpleGraph (Fin 8) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
noncomputable def coefficients : List ℚ := [0,-8,62,-174,241,-180,72,-14,1]
noncomputable def lowerMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![1,0,0,0,0,0,0,0;(-1/3),1,0,0,0,0,0,0;0,(-3/17),1,0,0,0,0,0;0,(-3/17),(-3/31),1,0,0,0,0;0,(-3/17),(-3/31),(-3/28),1,0,0,0;0,(-3/17),(-3/31),(-3/28),(-3/25),1,0,0;(-1/3),(-1/17),(-1/31),(-1/28),(-1/25),(-1/22),1,0;0,0,0,0,0,0,(-11/29),1],!![1,0,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0,0;0,(-4/27),1,0,0,0,0,0;0,(-4/27),(-4/77),1,0,0,0,0;0,(-4/27),(-4/77),(-4/73),1,0,0,0;0,(-4/27),(-4/77),(-4/73),(-4/69),1,0,0;(-1/4),(-1/27),(-1/77),(-1/73),(-1/69),(-1/65),1,0;0,0,0,0,0,0,(-65/243),1],!![1,0,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0,0;0,(-5/39),1,0,0,0,0,0;0,(-5/39),(-5/151),1,0,0,0,0;0,(-5/39),(-5/151),(-5/146),1,0,0,0;0,(-5/39),(-5/151),(-5/146),(-5/141),1,0,0;(-1/5),(-1/39),(-1/151),(-1/146),(-1/141),(-1/136),1,0;0,0,0,0,0,0,(-34/163),1],!![1,0,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0,0;0,(-6/53),1,0,0,0,0,0;0,(-6/53),(-6/259),1,0,0,0,0;0,(-6/53),(-6/259),(-6/253),1,0,0,0;0,(-6/53),(-6/259),(-6/253),(-6/247),1,0,0;(-1/6),(-1/53),(-1/259),(-1/253),(-1/247),(-1/241),1,0;0,0,0,0,0,0,(-241/1405),1],!![1,0,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0,0;0,(-7/69),1,0,0,0,0,0;0,(-7/69),(-7/407),1,0,0,0,0;0,(-7/69),(-7/407),(-7/400),1,0,0,0;0,(-7/69),(-7/407),(-7/400),(-7/393),1,0,0;(-1/7),(-1/69),(-1/407),(-1/400),(-1/393),(-1/386),1,0;0,0,0,0,0,0,(-193/1323),1],!![1,0,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0,0;0,(-8/87),1,0,0,0,0,0;0,(-8/87),(-8/601),1,0,0,0,0;0,(-8/87),(-8/601),(-8/593),1,0,0,0;0,(-8/87),(-8/601),(-8/593),(-8/585),1,0,0;(-1/8),(-1/87),(-1/601),(-1/593),(-1/585),(-1/577),1,0;0,0,0,0,0,0,(-577/4543),1],!![1,0,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0,0;0,(-9/107),1,0,0,0,0,0;0,(-9/107),(-9/847),1,0,0,0,0;0,(-9/107),(-9/847),(-9/838),1,0,0,0;0,(-9/107),(-9/847),(-9/838),(-9/829),1,0,0;(-1/9),(-1/107),(-1/847),(-1/838),(-1/829),(-1/820),1,0;0,0,0,0,0,0,(-205/1822),1],!![1,0,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0,0;0,(-10/129),1,0,0,0,0,0;0,(-10/129),(-10/1151),1,0,0,0,0;0,(-10/129),(-10/1151),(-10/1141),1,0,0,0;0,(-10/129),(-10/1151),(-10/1141),(-10/1131),1,0,0;(-1/10),(-1/129),(-1/1151),(-1/1141),(-1/1131),(-1/1121),1,0;0,0,0,0,0,0,(-1121/11097),1],!![1,0,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0,0;0,(-11/153),1,0,0,0,0,0;0,(-11/153),(-11/1519),1,0,0,0,0;0,(-11/153),(-11/1519),(-11/1508),1,0,0,0;0,(-11/153),(-11/1519),(-11/1508),(-11/1497),1,0,0;(-1/11),(-1/153),(-1/1519),(-1/1508),(-1/1497),(-1/1486),1,0;0,0,0,0,0,0,(-743/8105),1]]
noncomputable def upperMatrices : Fin 9 → Matrix (Fin 8) (Fin 8) ℚ := ![!![-3,1,0,0,0,0,1,0;0,(-17/3),1,1,1,1,(1/3),0;0,0,(-31/17),(3/17),(3/17),(3/17),(1/17),0;0,0,0,(-56/31),(6/31),(6/31),(2/31),0;0,0,0,0,(-25/14),(3/14),(1/14),0;0,0,0,0,0,(-44/25),(2/25),0;0,0,0,0,0,0,(-29/11),1;0,0,0,0,0,0,0,(-47/29)],!![-4,1,0,0,0,0,1,0;0,(-27/4),1,1,1,1,(1/4),0;0,0,(-77/27),(4/27),(4/27),(4/27),(1/27),0;0,0,0,(-219/77),(12/77),(12/77),(3/77),0;0,0,0,0,(-207/73),(12/73),(3/73),0;0,0,0,0,0,(-65/23),(1/23),0;0,0,0,0,0,0,(-243/65),1;0,0,0,0,0,0,0,(-664/243)],!![-5,1,0,0,0,0,1,0;0,(-39/5),1,1,1,1,(1/5),0;0,0,(-151/39),(5/39),(5/39),(5/39),(1/39),0;0,0,0,(-584/151),(20/151),(20/151),(4/151),0;0,0,0,0,(-282/73),(10/73),(2/73),0;0,0,0,0,0,(-544/141),(4/141),0;0,0,0,0,0,0,(-163/34),1;0,0,0,0,0,0,0,(-618/163)],!![-6,1,0,0,0,0,1,0;0,(-53/6),1,1,1,1,(1/6),0;0,0,(-259/53),(6/53),(6/53),(6/53),(1/53),0;0,0,0,(-1265/259),(30/259),(30/259),(5/259),0;0,0,0,0,(-1235/253),(30/253),(5/253),0;0,0,0,0,0,(-1205/247),(5/247),0;0,0,0,0,0,0,(-1405/241),1;0,0,0,0,0,0,0,(-6784/1405)],!![-7,1,0,0,0,0,1,0;0,(-69/7),1,1,1,1,(1/7),0;0,0,(-407/69),(7/69),(7/69),(7/69),(1/69),0;0,0,0,(-2400/407),(42/407),(42/407),(6/407),0;0,0,0,0,(-1179/200),(21/200),(3/200),0;0,0,0,0,0,(-772/131),(2/131),0;0,0,0,0,0,0,(-1323/193),1;0,0,0,0,0,0,0,(-7745/1323)],!![-8,1,0,0,0,0,1,0;0,(-87/8),1,1,1,1,(1/8),0;0,0,(-601/87),(8/87),(8/87),(8/87),(1/87),0;0,0,0,(-4151/601),(56/601),(56/601),(7/601),0;0,0,0,0,(-4095/593),(56/593),(7/593),0;0,0,0,0,0,(-4039/585),(7/585),0;0,0,0,0,0,0,(-4543/577),1;0,0,0,0,0,0,0,(-31224/4543)],!![-9,1,0,0,0,0,1,0;0,(-107/9),1,1,1,1,(1/9),0;0,0,(-847/107),(9/107),(9/107),(9/107),(1/107),0;0,0,0,(-6704/847),(72/847),(72/847),(8/847),0;0,0,0,0,(-3316/419),(36/419),(4/419),0;0,0,0,0,0,(-6560/829),(8/829),0;0,0,0,0,0,0,(-1822/205),1;0,0,0,0,0,0,0,(-14371/1822)],!![-10,1,0,0,0,0,1,0;0,(-129/10),1,1,1,1,(1/10),0;0,0,(-1151/129),(10/129),(10/129),(10/129),(1/129),0;0,0,0,(-10269/1151),(90/1151),(90/1151),(9/1151),0;0,0,0,0,(-10179/1141),(90/1141),(9/1141),0;0,0,0,0,0,(-3363/377),(3/377),0;0,0,0,0,0,0,(-11097/1121),1;0,0,0,0,0,0,0,(-98752/11097)],!![-11,1,0,0,0,0,1,0;0,(-153/11),1,1,1,1,(1/11),0;0,0,(-1519/153),(11/153),(11/153),(11/153),(1/153),0;0,0,0,(-15080/1519),(110/1519),(110/1519),(10/1519),0;0,0,0,0,(-7485/754),(55/754),(5/754),0;0,0,0,0,0,(-14860/1497),(10/1497),0;0,0,0,0,0,0,(-8105/743),1;0,0,0,0,0,0,0,(-80307/8105)]]
theorem matrix_certificates : ∀ k : Fin 9,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
noncomputable def boxes : List FactoredRoots.Box := [{coefficients := [0,8,-38,36,-11,1],count := 5,lower := ![(-15/536870912),(148931681/536870912),(12639593/8388608),(1697070579/536870912),(1625321891/268435456)],upper := ![(1/268435456),(74465849/268435456),(808933969/536870912),(424267649/134217728),(3250643799/536870912)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(536870899/536870912)],upper := ![(134217729/134217728)],copies := 3}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((3068666169/536870912) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/8) ∧
    stopLoss (laplacianSpectrum graph) (2-2/8) ≤ ((3068666203/536870912) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum003
