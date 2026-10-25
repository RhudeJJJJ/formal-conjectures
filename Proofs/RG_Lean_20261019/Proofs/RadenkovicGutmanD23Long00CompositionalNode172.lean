/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode171
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[46,0],[0]],[[0,0],[0]],[[690,0],[0]],[[0,0],[0]],[[4324,0],[0]],[[0,0],[0]],[[14674,0],[0]],[[0,0],[0]],[[29256,0],[0]],[[0,0],[0]],[[34822,23],[23]],[[0,0],[0]],[[24012,161],[161]],[[0,0],[0]],[[8694,368],[368]],[[0,0],[0]],[[1242,299],[299]],[[0,0],[0]],[[0,69],[69]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
