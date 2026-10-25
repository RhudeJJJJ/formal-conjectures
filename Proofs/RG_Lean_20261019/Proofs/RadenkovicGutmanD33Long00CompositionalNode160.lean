/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode159
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-31],[0]],[[0,0],[0]],[[-465,0],[0,0]],[[0,0],[0,0]],[[-2914,0],[0,0]],[[0,0],[0,0]],[[-9889,0],[0,0]],[[0,0],[0,0]],[[-19716,0],[0,0]],[[0,0],[0,0]],[[-23436,-31],[-31,0]],[[0,0],[0,0]],[[-15934,-248],[-248,0]],[[0,0],[0,0]],[[-5177,-682],[-682,0]],[[0,0],[0,0]],[[-93,-744],[-744,0]],[[0,0],[0,0]],[[279,-279],[-279,0]],[[0],[0,0]],[[0],[0,-31]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
