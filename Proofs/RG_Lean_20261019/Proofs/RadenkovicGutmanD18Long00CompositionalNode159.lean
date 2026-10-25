/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode037
import Proofs.RadenkovicGutmanD18Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-240,0],[0,0]],[[0,0],[0,0]],[[-1504,0],[0,0]],[[0,0],[0,0]],[[-5104,0],[0,0]],[[0,0],[0,0]],[[-10176,0],[0,0]],[[0,0],[0,0]],[[-12096,-16],[-16,0]],[[0,0],[0,0]],[[-8224,-128],[-128,0]],[[0,0],[0,0]],[[-2672,-352],[-352,0]],[[0,0],[0,0]],[[-48,-384],[-384,0]],[[0,0],[0,0]],[[144,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
