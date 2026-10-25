/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode159
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-180,0],[0,0]],[[0,0],[0,0]],[[-1128,0],[0,0]],[[0,0],[0,0]],[[-3828,0],[0,0]],[[0,0],[0,0]],[[-7632,0],[0,0]],[[0,0],[0,0]],[[-9072,-12],[-12,0]],[[0,0],[0,0]],[[-6168,-96],[-96,0]],[[0,0],[0,0]],[[-2004,-264],[-264,0]],[[0,0],[0,0]],[[-36,-288],[-288,0]],[[0,0],[0,0]],[[108,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
