/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode034
import Proofs.RadenkovicGutmanD8Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-128,0],[0]],[[0,0],[0]],[[-856,0],[0]],[[0,0],[0]],[[-3104,0],[0]],[[0,0],[0]],[[-6624,0],[0]],[[0,0],[0]],[[-8448,-8],[-8]],[[0,0],[0]],[[-6232,-56],[-56]],[[0,0],[0]],[[-2400,-128],[-128]],[[0,0],[0]],[[-360,-104],[-104]],[[0,0],[0]],[[0,-24],[-24]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
