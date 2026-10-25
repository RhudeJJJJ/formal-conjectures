/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode119
import Proofs.RadenkovicGutmanD10Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-232,0],[0,0]],[[0,0],[0,0]],[[-1392,0],[0,0]],[[0,0],[0,0]],[[-4456,0],[0,0]],[[0,0],[0,0]],[[-8176,0],[0,0]],[[0,0],[0,0]],[[-8544,-16],[-16,0]],[[0,0],[0,0]],[[-4560,-128],[-128,0]],[[0,0],[0,0]],[[-552,-352],[-352,0]],[[0,0],[0,0]],[[576,-384],[-384,0]],[[0,0],[0,0]],[[216,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
