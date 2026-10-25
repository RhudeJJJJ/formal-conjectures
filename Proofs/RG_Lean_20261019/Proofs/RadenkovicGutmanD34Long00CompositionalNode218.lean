/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode034
import Proofs.RadenkovicGutmanD34Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-544,0],[0]],[[0,0],[0]],[[-3638,0],[0]],[[0,0],[0]],[[-13192,0],[0]],[[0,0],[0]],[[-28152,0],[0]],[[0,0],[0]],[[-35904,-34],[-34]],[[0,0],[0]],[[-26486,-238],[-238]],[[0,0],[0]],[[-10200,-544],[-544]],[[0,0],[0]],[[-1530,-442],[-442]],[[0,0],[0]],[[0,-102],[-102]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
