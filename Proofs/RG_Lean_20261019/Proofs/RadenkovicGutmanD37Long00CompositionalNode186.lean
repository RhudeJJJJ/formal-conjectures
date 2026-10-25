/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode178
import Proofs.RadenkovicGutmanD37Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-70],[0]],[[0,0],[0]],[[-1153,0],[0,0]],[[0,0],[0,0]],[[-7948,0],[0,0]],[[0,0],[0,0]],[[-29711,0],[0,0]],[[0,0],[0,0]],[[-65164,0],[0,0]],[[0,0],[0,0]],[[-84444,-70],[-70,0]],[[0,0],[0,0]],[[-61028,-523],[-523,0]],[[0,0],[0,0]],[[-19967,-1281],[-1281,0]],[[0,0],[0,0]],[[-30,-1088],[-1088,0]],[[0,0],[0,0]],[[1035,-149],[-149,0]],[[0,0],[0,0]],[[0,111],[111,-70]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
