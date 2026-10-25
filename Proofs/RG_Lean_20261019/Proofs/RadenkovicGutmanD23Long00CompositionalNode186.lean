/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode178
import Proofs.RadenkovicGutmanD23Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-691,0],[0,0]],[[0,0],[0,0]],[[-4756,0],[0,0]],[[0,0],[0,0]],[[-17741,0],[0,0]],[[0,0],[0,0]],[[-38788,0],[0,0]],[[0,0],[0,0]],[[-50004,-42],[-42,0]],[[0,0],[0,0]],[[-35772,-313],[-313,0]],[[0,0],[0,0]],[[-11357,-763],[-763,0]],[[0,0],[0,0]],[[222,-640],[-640,0]],[[0,0],[0,0]],[[657,-79],[-79,0]],[[0,0],[0,0]],[[0,69],[69,-42]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
