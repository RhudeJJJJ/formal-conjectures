/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode045
import Proofs.RadenkovicGutmanD30Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0,0]],[[-270,450],[450,2]],[[0,0],[0]],[[3312,1518],[1518]],[[0,0],[0]],[[27696,1668],[1668]],[[0,0],[0]],[[78394,704],[704]],[[0,0],[0]],[[114548,106],[106]],[[0,0],[0]],[[96912,2],[2]],[[0]],[[49122]],[[0]],[[14738]],[[0]],[[2438]],[[0]],[[180]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
