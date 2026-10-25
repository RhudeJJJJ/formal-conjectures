/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode034
import Proofs.RadenkovicGutmanD18Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-288,0],[0]],[[0,0],[0]],[[-1926,0],[0]],[[0,0],[0]],[[-6984,0],[0]],[[0,0],[0]],[[-14904,0],[0]],[[0,0],[0]],[[-19008,-18],[-18]],[[0,0],[0]],[[-14022,-126],[-126]],[[0,0],[0]],[[-5400,-288],[-288]],[[0,0],[0]],[[-810,-234],[-234]],[[0,0],[0]],[[0,-54],[-54]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
