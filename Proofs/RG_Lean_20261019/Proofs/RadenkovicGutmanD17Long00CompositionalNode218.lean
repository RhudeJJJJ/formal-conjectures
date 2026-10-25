/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode034
import Proofs.RadenkovicGutmanD17Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-17],[0]],[[0,0],[0]],[[-272,0],[0]],[[0,0],[0]],[[-1819,0],[0]],[[0,0],[0]],[[-6596,0],[0]],[[0,0],[0]],[[-14076,0],[0]],[[0,0],[0]],[[-17952,-17],[-17]],[[0,0],[0]],[[-13243,-119],[-119]],[[0,0],[0]],[[-5100,-272],[-272]],[[0,0],[0]],[[-765,-221],[-221]],[[0,0],[0]],[[0,-51],[-51]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
