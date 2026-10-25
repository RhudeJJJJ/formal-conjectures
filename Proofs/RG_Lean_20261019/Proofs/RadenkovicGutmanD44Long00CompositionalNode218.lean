/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode034
import Proofs.RadenkovicGutmanD44Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-704,0],[0]],[[0,0],[0]],[[-4708,0],[0]],[[0,0],[0]],[[-17072,0],[0]],[[0,0],[0]],[[-36432,0],[0]],[[0,0],[0]],[[-46464,-44],[-44]],[[0,0],[0]],[[-34276,-308],[-308]],[[0,0],[0]],[[-13200,-704],[-704]],[[0,0],[0]],[[-1980,-572],[-572]],[[0,0],[0]],[[0,-132],[-132]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
