/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode034
import Proofs.RadenkovicGutmanD42Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-672,0],[0]],[[0,0],[0]],[[-4494,0],[0]],[[0,0],[0]],[[-16296,0],[0]],[[0,0],[0]],[[-34776,0],[0]],[[0,0],[0]],[[-44352,-42],[-42]],[[0,0],[0]],[[-32718,-294],[-294]],[[0,0],[0]],[[-12600,-672],[-672]],[[0,0],[0]],[[-1890,-546],[-546]],[[0,0],[0]],[[0,-126],[-126]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
