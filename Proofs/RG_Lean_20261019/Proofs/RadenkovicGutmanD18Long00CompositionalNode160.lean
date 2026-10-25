/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode159
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-240,0],[0,0]],[[0,0],[0,0]],[[-1504,0],[0,0]],[[0,0],[0,0]],[[-5104,0],[0,0]],[[0,0],[0,0]],[[-10176,0],[0,0]],[[0,0],[0,0]],[[-12096,-16],[-16,0]],[[0,0],[0,0]],[[-8224,-128],[-128,0]],[[0,0],[0,0]],[[-2672,-352],[-352,0]],[[0,0],[0,0]],[[-48,-384],[-384,0]],[[0,0],[0,0]],[[144,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
