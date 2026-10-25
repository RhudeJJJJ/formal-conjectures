/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode045
import Proofs.RadenkovicGutmanD15Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,15]],[[0,0],[0,0]],[[-135,225],[225,2]],[[0,0],[0]],[[1647,768],[768]],[[0,0],[0]],[[13851,858],[858]],[[0,0],[0]],[[39364,374],[374]],[[0,0],[0]],[[57788,61],[61]],[[0,0],[0]],[[49212,2],[2]],[[0]],[[25197]],[[0]],[[7688]],[[0]],[[1313]],[[0]],[[105]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
