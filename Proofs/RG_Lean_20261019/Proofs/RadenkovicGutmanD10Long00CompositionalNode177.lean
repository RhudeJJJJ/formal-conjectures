/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode174
import Proofs.RadenkovicGutmanD10Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-272,0],[0,0]],[[0,0],[0,0]],[[-1952,0],[0,0]],[[0,0],[0,0]],[[-7696,0],[0,0]],[[0,0],[0,0]],[[-18176,0],[0,0]],[[0,0],[0,0]],[[-26304,-16],[-16,0]],[[0,0],[0,0]],[[-22880,-128],[-128,0]],[[0,0],[0,0]],[[-11152,-352],[-352,0]],[[0,0],[0,0]],[[-2544,-384],[-384,0]],[[0,0],[0,0]],[[-144,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
