/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode159
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-600,0],[0,0]],[[0,0],[0,0]],[[-3760,0],[0,0]],[[0,0],[0,0]],[[-12760,0],[0,0]],[[0,0],[0,0]],[[-25440,0],[0,0]],[[0,0],[0,0]],[[-30240,-40],[-40,0]],[[0,0],[0,0]],[[-20560,-320],[-320,0]],[[0,0],[0,0]],[[-6680,-880],[-880,0]],[[0,0],[0,0]],[[-120,-960],[-960,0]],[[0,0],[0,0]],[[360,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
