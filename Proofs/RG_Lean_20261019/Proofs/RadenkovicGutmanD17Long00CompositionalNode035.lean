/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode034
import Proofs.RadenkovicGutmanD17Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-51],[-51]],[[0,0],[0]],[[-918,-221],[-221]],[[0,0],[0]],[[-6426,-272],[-272]],[[0,0],[0]],[[-17748,-119],[-119]],[[0,0],[0]],[[-25738,-17],[-17]],[[0]],[[-21624]],[[0]],[[-10846]],[[0]],[[-3196]],[[0]],[[-510]],[[0]],[[-34]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
