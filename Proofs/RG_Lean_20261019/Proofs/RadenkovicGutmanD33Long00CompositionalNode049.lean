/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode045
import Proofs.RadenkovicGutmanD33Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0,0]],[[-297,495],[495,2]],[[0,0],[0]],[[3645,1668],[1668]],[[0,0],[0]],[[30465,1830],[1830]],[[0,0],[0]],[[86200,770],[770]],[[0,0],[0]],[[125900,115],[115]],[[0,0],[0]],[[106452,2],[2]],[[0]],[[53907]],[[0]],[[16148]],[[0]],[[2663]],[[0]],[[195]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
