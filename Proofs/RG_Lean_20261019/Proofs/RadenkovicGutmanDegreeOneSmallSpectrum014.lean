/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum014
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,false,false,true,false,true],![true,false,true,true,false,false,false],![false,true,false,false,false,false,false],![false,true,false,false,false,false,false],![true,false,false,false,false,true,false],![false,false,false,false,true,false,false],![true,false,false,false,false,false,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-46,105,-108,53,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/4),1,0,0,0,0,0;0,(-4/15),1,0,0,0,0;0,(-4/15),(-2/13),1,0,0,0;(-1/4),(-1/15),(-1/26),(-1/22),1,0,0;0,0,0,0,(-11/30),1,0;(-1/4),(-1/15),(-1/26),(-1/22),(-1/10),(-3/49),1],!![1,0,0,0,0,0,0;(-1/5),1,0,0,0,0,0;0,(-5/24),1,0,0,0,0;0,(-5/24),(-5/67),1,0,0,0;(-1/5),(-1/24),(-1/67),(-1/62),1,0,0;0,0,0,0,(-62/235),1,0;(-1/5),(-1/24),(-1/67),(-1/62),(-13/235),(-13/643),1],!![1,0,0,0,0,0,0;(-1/6),1,0,0,0,0,0;0,(-6/35),1,0,0,0,0;0,(-6/35),(-3/67),1,0,0,0;(-1/6),(-1/35),(-1/134),(-1/128),1,0,0;0,0,0,0,(-64/309),1,0;(-1/6),(-1/35),(-1/134),(-1/128),(-11/309),(-11/1172),1],!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;0,(-7/48),1,0,0,0,0;0,(-7/48),(-7/233),1,0,0,0;(-1/7),(-1/48),(-1/233),(-1/226),1,0,0;0,0,0,0,(-226/1323),1,0;(-1/7),(-1/48),(-1/233),(-1/226),(-11/441),(-33/6389),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;0,(-8/63),1,0,0,0,0;0,(-8/63),(-4/185),1,0,0,0;(-1/8),(-1/63),(-1/370),(-1/362),1,0,0;0,0,0,0,(-181/1244),1,0;(-1/8),(-1/63),(-1/370),(-1/362),(-23/1244),(-23/7283),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;0,(-9/80),1,0,0,0,0;0,(-9/80),(-9/551),1,0,0,0;(-1/9),(-1/80),(-1/551),(-1/542),1,0,0;0,0,0,0,(-542/4275),1,0;(-1/9),(-1/80),(-1/551),(-1/542),(-61/4275),(-61/29383),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;0,(-10/99),1,0,0,0,0;0,(-10/99),(-5/391),1,0,0,0;(-1/10),(-1/99),(-1/782),(-1/772),1,0,0;0,0,0,0,(-386/3435),1,0;(-1/10),(-1/99),(-1/782),(-1/772),(-13/1145),(-39/27094),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;0,(-11/120),1,0,0,0,0;0,(-11/120),(-11/1069),1,0,0,0;(-1/11),(-1/120),(-1/1069),(-1/1058),1,0,0;0,0,0,0,(-1058/10483),1,0;(-1/11),(-1/120),(-1/1069),(-1/1058),(-97/10483),(-97/93289),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-4,1,0,0,1,0,1;0,(-15/4),1,1,(1/4),0,(1/4);0,0,(-26/15),(4/15),(1/15),0,(1/15);0,0,0,(-22/13),(1/13),0,(1/13);0,0,0,0,(-30/11),1,(3/11);0,0,0,0,0,(-49/30),(1/10);0,0,0,0,0,0,(-83/49)],!![-5,1,0,0,1,0,1;0,(-24/5),1,1,(1/5),0,(1/5);0,0,(-67/24),(5/24),(1/24),0,(1/24);0,0,0,(-186/67),(3/67),0,(3/67);0,0,0,0,(-235/62),1,(13/62);0,0,0,0,0,(-643/235),(13/235);0,0,0,0,0,0,(-1786/643)],!![-6,1,0,0,1,0,1;0,(-35/6),1,1,(1/6),0,(1/6);0,0,(-134/35),(6/35),(1/35),0,(1/35);0,0,0,(-256/67),(2/67),0,(2/67);0,0,0,0,(-309/64),1,(11/64);0,0,0,0,0,(-1172/309),(11/309);0,0,0,0,0,0,(-4479/1172)],!![-7,1,0,0,1,0,1;0,(-48/7),1,1,(1/7),0,(1/7);0,0,(-233/48),(7/48),(1/48),0,(1/48);0,0,0,(-1130/233),(5/233),0,(5/233);0,0,0,0,(-1323/226),1,(33/226);0,0,0,0,0,(-6389/1323),(11/441);0,0,0,0,0,0,(-30988/6389)],!![-8,1,0,0,1,0,1;0,(-63/8),1,1,(1/8),0,(1/8);0,0,(-370/63),(8/63),(1/63),0,(1/63);0,0,0,(-1086/185),(3/185),0,(3/185);0,0,0,0,(-1244/181),1,(23/181);0,0,0,0,0,(-7283/1244),(23/1244);0,0,0,0,0,0,(-42755/7283)],!![-9,1,0,0,1,0,1;0,(-80/9),1,1,(1/9),0,(1/9);0,0,(-551/80),(9/80),(1/80),0,(1/80);0,0,0,(-3794/551),(7/551),0,(7/551);0,0,0,0,(-4275/542),1,(61/542);0,0,0,0,0,(-29383/4275),(61/4275);0,0,0,0,0,0,(-202326/29383)],!![-10,1,0,0,1,0,1;0,(-99/10),1,1,(1/10),0,(1/10);0,0,(-782/99),(10/99),(1/99),0,(1/99);0,0,0,(-3088/391),(4/391),0,(4/391);0,0,0,0,(-3435/386),1,(39/386);0,0,0,0,0,(-27094/3435),(13/1145);0,0,0,0,0,0,(-213983/27094)],!![-11,1,0,0,1,0,1;0,(-120/11),1,1,(1/11),0,(1/11);0,0,(-1069/120),(11/120),(1/120),0,(1/120);0,0,0,(-9522/1069),(9/1069),0,(9/1069);0,0,0,0,(-10483/1058),1,(97/1058);0,0,0,0,0,(-93289/10483),(97/10483);0,0,0,0,0,0,(-830968/93289)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,7,-46,105,-108,53,-12,1],count := 7,lower := ![(-1/268435456),(43180477/134217728),(91298287/134217728),(134217727/134217728),(143590541/67108864),(433488097/134217728),(621247057/134217728)],upper := ![(7/134217728),(86360969/268435456),(182596589/268435456),(268435469/268435456),(574362179/268435456),(866976209/268435456),(1242494129/268435456)],copies := 1}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  
theorem actual_graph_bounds :
    ((1140393861/234881024) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((9123151203/1879048192) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.DegreeOneSmallSpectrum014
