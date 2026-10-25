/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode045
import Proofs.RadenkovicGutmanD8Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0,0]],[[-72,120],[120,2]],[[0,0],[0]],[[870,418],[418]],[[0,0],[0]],[[7390,480],[480]],[[0,0],[0]],[[21150,220],[220]],[[0,0],[0]],[[31300,40],[40]],[[0,0],[0]],[[26952,2],[2]],[[0]],[[14032]],[[0]],[[4398]],[[0]],[[788]],[[0]],[[70]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
