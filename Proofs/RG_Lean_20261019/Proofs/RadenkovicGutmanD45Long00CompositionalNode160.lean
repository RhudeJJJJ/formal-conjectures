/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode159
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-43],[0]],[[0,0],[0]],[[-645,0],[0,0]],[[0,0],[0,0]],[[-4042,0],[0,0]],[[0,0],[0,0]],[[-13717,0],[0,0]],[[0,0],[0,0]],[[-27348,0],[0,0]],[[0,0],[0,0]],[[-32508,-43],[-43,0]],[[0,0],[0,0]],[[-22102,-344],[-344,0]],[[0,0],[0,0]],[[-7181,-946],[-946,0]],[[0,0],[0,0]],[[-129,-1032],[-1032,0]],[[0,0],[0,0]],[[387,-387],[-387,0]],[[0],[0,0]],[[0],[0,-43]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
