/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode177
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-272,0],[0,0]],[[0,0],[0,0]],[[-1952,0],[0,0]],[[0,0],[0,0]],[[-7696,0],[0,0]],[[0,0],[0,0]],[[-18176,0],[0,0]],[[0,0],[0,0]],[[-26304,-16],[-16,0]],[[0,0],[0,0]],[[-22880,-128],[-128,0]],[[0,0],[0,0]],[[-11152,-352],[-352,0]],[[0,0],[0,0]],[[-2544,-384],[-384,0]],[[0,0],[0,0]],[[-144,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
