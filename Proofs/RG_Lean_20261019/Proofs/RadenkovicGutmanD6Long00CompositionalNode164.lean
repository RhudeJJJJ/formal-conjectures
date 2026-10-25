/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode119
import Proofs.RadenkovicGutmanD6Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-112,0],[0,0]],[[0,0],[0,0]],[[-640,0],[0,0]],[[0,0],[0,0]],[[-1904,0],[0,0]],[[0,0],[0,0]],[[-3088,0],[0,0]],[[0,0],[0,0]],[[-2496,-8],[-8,0]],[[0,0],[0,0]],[[-448,-64],[-64,0]],[[0,0],[0,0]],[[784,-176],[-176,0]],[[0,0],[0,0]],[[600,-192],[-192,0]],[[0,0],[0,0]],[[144,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
