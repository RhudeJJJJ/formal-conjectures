/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode178
import Proofs.RadenkovicGutmanD34Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-1054,0],[0,0]],[[0,0],[0,0]],[[-7264,0],[0,0]],[[0,0],[0,0]],[[-27146,0],[0,0]],[[0,0],[0,0]],[[-59512,0],[0,0]],[[0,0],[0,0]],[[-77064,-64],[-64,0]],[[0,0],[0,0]],[[-55616,-478],[-478,0]],[[0,0],[0,0]],[[-18122,-1170],[-1170,0]],[[0,0],[0,0]],[[24,-992],[-992,0]],[[0,0],[0,0]],[[954,-134],[-134,0]],[[0,0],[0,0]],[[0,102],[102,-64]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
