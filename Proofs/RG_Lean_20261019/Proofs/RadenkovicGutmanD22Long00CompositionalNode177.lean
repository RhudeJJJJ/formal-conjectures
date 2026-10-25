/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode174
import Proofs.RadenkovicGutmanD22Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-680,0],[0,0]],[[0,0],[0,0]],[[-4880,0],[0,0]],[[0,0],[0,0]],[[-19240,0],[0,0]],[[0,0],[0,0]],[[-45440,0],[0,0]],[[0,0],[0,0]],[[-65760,-40],[-40,0]],[[0,0],[0,0]],[[-57200,-320],[-320,0]],[[0,0],[0,0]],[[-27880,-880],[-880,0]],[[0,0],[0,0]],[[-6360,-960],[-960,0]],[[0,0],[0,0]],[[-360,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
