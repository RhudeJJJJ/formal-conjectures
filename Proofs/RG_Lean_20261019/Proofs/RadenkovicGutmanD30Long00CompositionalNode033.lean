/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0]],[[-270,270],[270]],[[0,0],[0]],[[90,720],[720]],[[0,0],[0]],[[5010,660],[660]],[[0,0],[0]],[[15420,240],[240]],[[0,0],[0]],[[22680,30],[30]],[[0]],[[19080]],[[0]],[[9570]],[[0]],[[2820]],[[0]],[[450]],[[0]],[[30]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
