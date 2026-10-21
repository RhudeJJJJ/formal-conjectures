/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteSpectralCertificates
namespace Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum001
open Matrix Polynomial Finset
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [-instance] SimpleGraph.fintypeEdgeSetSup
def adjacency : Fin 7 → Fin 7 → Bool := ![![false,true,true,true,true,true,true],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false],![true,false,false,false,false,false,false]]
def graph : SimpleGraph (Fin 7) where
  Adj i j := adjacency i j=true
  symm := by constructor; decide +kernel
  loopless := by constructor; decide +kernel
instance graphDecidable : DecidableRel graph.Adj := fun i j => inferInstanceAs (Decidable (adjacency i j=true))
def coefficients : List ℚ := [0,7,-36,75,-80,45,-12,1]
def lowerMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![1,0,0,0,0,0,0;(-1/7),1,0,0,0,0,0;(-1/7),(-1/13),1,0,0,0,0;(-1/7),(-1/13),(-1/12),1,0,0,0;(-1/7),(-1/13),(-1/12),(-1/11),1,0,0;(-1/7),(-1/13),(-1/12),(-1/11),(-1/10),1,0;(-1/7),(-1/13),(-1/12),(-1/11),(-1/10),(-1/9),1],!![1,0,0,0,0,0,0;(-1/8),1,0,0,0,0,0;(-1/8),(-1/23),1,0,0,0,0;(-1/8),(-1/23),(-1/22),1,0,0,0;(-1/8),(-1/23),(-1/22),(-1/21),1,0,0;(-1/8),(-1/23),(-1/22),(-1/21),(-1/20),1,0;(-1/8),(-1/23),(-1/22),(-1/21),(-1/20),(-1/19),1],!![1,0,0,0,0,0,0;(-1/9),1,0,0,0,0,0;(-1/9),(-1/35),1,0,0,0,0;(-1/9),(-1/35),(-1/34),1,0,0,0;(-1/9),(-1/35),(-1/34),(-1/33),1,0,0;(-1/9),(-1/35),(-1/34),(-1/33),(-1/32),1,0;(-1/9),(-1/35),(-1/34),(-1/33),(-1/32),(-1/31),1],!![1,0,0,0,0,0,0;(-1/10),1,0,0,0,0,0;(-1/10),(-1/49),1,0,0,0,0;(-1/10),(-1/49),(-1/48),1,0,0,0;(-1/10),(-1/49),(-1/48),(-1/47),1,0,0;(-1/10),(-1/49),(-1/48),(-1/47),(-1/46),1,0;(-1/10),(-1/49),(-1/48),(-1/47),(-1/46),(-1/45),1],!![1,0,0,0,0,0,0;(-1/11),1,0,0,0,0,0;(-1/11),(-1/65),1,0,0,0,0;(-1/11),(-1/65),(-1/64),1,0,0,0;(-1/11),(-1/65),(-1/64),(-1/63),1,0,0;(-1/11),(-1/65),(-1/64),(-1/63),(-1/62),1,0;(-1/11),(-1/65),(-1/64),(-1/63),(-1/62),(-1/61),1],!![1,0,0,0,0,0,0;(-1/12),1,0,0,0,0,0;(-1/12),(-1/83),1,0,0,0,0;(-1/12),(-1/83),(-1/82),1,0,0,0;(-1/12),(-1/83),(-1/82),(-1/81),1,0,0;(-1/12),(-1/83),(-1/82),(-1/81),(-1/80),1,0;(-1/12),(-1/83),(-1/82),(-1/81),(-1/80),(-1/79),1],!![1,0,0,0,0,0,0;(-1/13),1,0,0,0,0,0;(-1/13),(-1/103),1,0,0,0,0;(-1/13),(-1/103),(-1/102),1,0,0,0;(-1/13),(-1/103),(-1/102),(-1/101),1,0,0;(-1/13),(-1/103),(-1/102),(-1/101),(-1/100),1,0;(-1/13),(-1/103),(-1/102),(-1/101),(-1/100),(-1/99),1],!![1,0,0,0,0,0,0;(-1/14),1,0,0,0,0,0;(-1/14),(-1/125),1,0,0,0,0;(-1/14),(-1/125),(-1/124),1,0,0,0;(-1/14),(-1/125),(-1/124),(-1/123),1,0,0;(-1/14),(-1/125),(-1/124),(-1/123),(-1/122),1,0;(-1/14),(-1/125),(-1/124),(-1/123),(-1/122),(-1/121),1]]
def upperMatrices : Fin 8 → Matrix (Fin 7) (Fin 7) ℚ := ![!![-7,1,1,1,1,1,1;0,(-13/7),(1/7),(1/7),(1/7),(1/7),(1/7);0,0,(-24/13),(2/13),(2/13),(2/13),(2/13);0,0,0,(-11/6),(1/6),(1/6),(1/6);0,0,0,0,(-20/11),(2/11),(2/11);0,0,0,0,0,(-9/5),(1/5);0,0,0,0,0,0,(-16/9)],!![-8,1,1,1,1,1,1;0,(-23/8),(1/8),(1/8),(1/8),(1/8),(1/8);0,0,(-66/23),(3/23),(3/23),(3/23),(3/23);0,0,0,(-63/22),(3/22),(3/22),(3/22);0,0,0,0,(-20/7),(1/7),(1/7);0,0,0,0,0,(-57/20),(3/20);0,0,0,0,0,0,(-54/19)],!![-9,1,1,1,1,1,1;0,(-35/9),(1/9),(1/9),(1/9),(1/9),(1/9);0,0,(-136/35),(4/35),(4/35),(4/35),(4/35);0,0,0,(-66/17),(2/17),(2/17),(2/17);0,0,0,0,(-128/33),(4/33),(4/33);0,0,0,0,0,(-31/8),(1/8);0,0,0,0,0,0,(-120/31)],!![-10,1,1,1,1,1,1;0,(-49/10),(1/10),(1/10),(1/10),(1/10),(1/10);0,0,(-240/49),(5/49),(5/49),(5/49),(5/49);0,0,0,(-235/48),(5/48),(5/48),(5/48);0,0,0,0,(-230/47),(5/47),(5/47);0,0,0,0,0,(-225/46),(5/46);0,0,0,0,0,0,(-44/9)],!![-11,1,1,1,1,1,1;0,(-65/11),(1/11),(1/11),(1/11),(1/11),(1/11);0,0,(-384/65),(6/65),(6/65),(6/65),(6/65);0,0,0,(-189/32),(3/32),(3/32),(3/32);0,0,0,0,(-124/21),(2/21),(2/21);0,0,0,0,0,(-183/31),(3/31);0,0,0,0,0,0,(-360/61)],!![-12,1,1,1,1,1,1;0,(-83/12),(1/12),(1/12),(1/12),(1/12),(1/12);0,0,(-574/83),(7/83),(7/83),(7/83),(7/83);0,0,0,(-567/82),(7/82),(7/82),(7/82);0,0,0,0,(-560/81),(7/81),(7/81);0,0,0,0,0,(-553/80),(7/80);0,0,0,0,0,0,(-546/79)],!![-13,1,1,1,1,1,1;0,(-103/13),(1/13),(1/13),(1/13),(1/13),(1/13);0,0,(-816/103),(8/103),(8/103),(8/103),(8/103);0,0,0,(-404/51),(4/51),(4/51),(4/51);0,0,0,0,(-800/101),(8/101),(8/101);0,0,0,0,0,(-198/25),(2/25);0,0,0,0,0,0,(-784/99)],!![-14,1,1,1,1,1,1;0,(-125/14),(1/14),(1/14),(1/14),(1/14),(1/14);0,0,(-1116/125),(9/125),(9/125),(9/125),(9/125);0,0,0,(-1107/124),(9/124),(9/124),(9/124);0,0,0,0,(-366/41),(3/41),(3/41);0,0,0,0,0,(-1089/122),(9/122);0,0,0,0,0,0,(-1080/121)]]
theorem matrix_certificates : ∀ k : Fin 8,
    CheckedCharpoly.acceptsLU
      (CheckedCharpoly.shifted (CheckedCharpoly.laplacian (fun i j => decide (graph.Adj i j)))
        (CheckedCharpoly.sample k)) (lowerMatrices k) (upperMatrices k)
      (CheckedRoots.eval coefficients (CheckedCharpoly.sample k))=true := by decide +kernel
theorem graph_charpoly : (graph.lapMatrix ℝ).charpoly=CheckedRoots.polynomial coefficients :=
  FiniteSpectralCertificates.graph_polynomial graph coefficients (by decide)
    lowerMatrices upperMatrices matrix_certificates
def boxes : List FactoredRoots.Box := [{coefficients := [0,-7,1],count := 2,lower := ![(-1/268435456),(234881023/33554432)],upper := ![(7/134217728),(1879048199/268435456)],copies := 1},{coefficients := [-1,1],count := 1,lower := ![(134217727/134217728)],upper := ![(268435469/268435456)],copies := 5}]
theorem boxes_accepted : FactoredRoots.allAccepted boxes=true := by decide +kernel
theorem factorization : CheckedRoots.polynomial coefficients=FactoredRoots.product boxes := by
  norm_num [coefficients,boxes,CheckedRoots.polynomial,FactoredRoots.product,FactoredRoots.factor,
    Polynomial.C_ofNat]
  ring
theorem actual_graph_bounds :
    ((1241513977/234881024) : ℝ) ≤ stopLoss (laplacianSpectrum graph) (2-2/7) ∧
    stopLoss (laplacianSpectrum graph) (2-2/7) ≤ ((9932111921/1879048192) : ℝ) := by
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
end Gebendorfer.RadenkovicGutman.SmallGeFourSpectrum001
