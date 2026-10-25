/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode037
import Proofs.RadenkovicGutmanD14Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-180,0],[0,0]],[[0,0],[0,0]],[[-1128,0],[0,0]],[[0,0],[0,0]],[[-3828,0],[0,0]],[[0,0],[0,0]],[[-7632,0],[0,0]],[[0,0],[0,0]],[[-9072,-12],[-12,0]],[[0,0],[0,0]],[[-6168,-96],[-96,0]],[[0,0],[0,0]],[[-2004,-264],[-264,0]],[[0,0],[0,0]],[[-36,-288],[-288,0]],[[0,0],[0,0]],[[108,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
