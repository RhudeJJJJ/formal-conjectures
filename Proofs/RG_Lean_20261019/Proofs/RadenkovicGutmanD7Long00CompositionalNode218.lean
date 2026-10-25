/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode034
import Proofs.RadenkovicGutmanD7Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-7],[0]],[[0,0],[0]],[[-112,0],[0]],[[0,0],[0]],[[-749,0],[0]],[[0,0],[0]],[[-2716,0],[0]],[[0,0],[0]],[[-5796,0],[0]],[[0,0],[0]],[[-7392,-7],[-7]],[[0,0],[0]],[[-5453,-49],[-49]],[[0,0],[0]],[[-2100,-112],[-112]],[[0,0],[0]],[[-315,-91],[-91]],[[0,0],[0]],[[0,-21],[-21]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
