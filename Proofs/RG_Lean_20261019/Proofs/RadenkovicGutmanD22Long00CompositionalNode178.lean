/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode177
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-680,0],[0,0]],[[0,0],[0,0]],[[-4880,0],[0,0]],[[0,0],[0,0]],[[-19240,0],[0,0]],[[0,0],[0,0]],[[-45440,0],[0,0]],[[0,0],[0,0]],[[-65760,-40],[-40,0]],[[0,0],[0,0]],[[-57200,-320],[-320,0]],[[0,0],[0,0]],[[-27880,-880],[-880,0]],[[0,0],[0,0]],[[-6360,-960],[-960,0]],[[0,0],[0,0]],[[-360,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
