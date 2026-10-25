/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode178
import Proofs.RadenkovicGutmanD10Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-262,0],[0,0]],[[0,0],[0,0]],[[-1792,0],[0,0]],[[0,0],[0,0]],[[-6626,0],[0,0]],[[0,0],[0,0]],[[-14296,0],[0,0]],[[0,0],[0,0]],[[-18024,-16],[-16,0]],[[0,0],[0,0]],[[-12320,-118],[-118,0]],[[0,0],[0,0]],[[-3362,-282],[-282,0]],[[0,0],[0,0]],[[456,-224],[-224,0]],[[0,0],[0,0]],[[306,-14],[-14,0]],[[0,0],[0,0]],[[0,30],[30,-16]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
