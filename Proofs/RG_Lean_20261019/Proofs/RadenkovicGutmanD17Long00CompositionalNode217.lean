/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode034
import Proofs.RadenkovicGutmanD17Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-510,0],[0]],[[0,0],[0]],[[-3196,0],[0]],[[0,0],[0]],[[-10846,0],[0]],[[0,0],[0]],[[-21624,0],[0]],[[0,0],[0]],[[-25738,-17],[-17]],[[0,0],[0]],[[-17748,-119],[-119]],[[0,0],[0]],[[-6426,-272],[-272]],[[0,0],[0]],[[-918,-221],[-221]],[[0,0],[0]],[[0,-51],[-51]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
