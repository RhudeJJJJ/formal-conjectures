/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode071
import Proofs.RadenkovicGutmanD5Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1350,0],[-1350,-585,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25515,-28215,0],[-28215,-6060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-539055,-236430,0],[-236430,-25805,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4962330,-1087655,0],[-1087655,-58920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26679645,-3117650,0],[-3117650,-79240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-94452015,-5949365,0],[-5949365,-65090,0],[0,0]],[[0,0,0],[0,0],[0]],[[-234964960,-7856310,0],[-7856310,-32765],[0]],[[0,0,0],[0,0],[0]],[[-427489440,-7344140,0],[-7344140,-9820],[0]],[[0,0,0],[0,0],[0]],[[-583861235,-4915510,0],[-4915510,-1605],[0]],[[0,0,0],[0,0],[0]],[[-608987080,-2358615,0],[-2358615,-110],[0]],[[0,0,0],[0,0],[0]],[[-490296910,-803310,0],[-803310,0],[0]],[[0,0],[0]],[[-306338300,-189325],[-189325]],[[0,0],[0]],[[-148605755,-29330],[-29330]],[[0,0],[0]],[[-55704535,-2685],[-2685]],[[0,0],[0]],[[-15956440,-110],[-110]],[[0,0],[0]],[[-3424100,0],[0]],[[0]],[[-532325]],[[0]],[[-56575]],[[0]],[[-3675]],[[0]],[[-110]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
