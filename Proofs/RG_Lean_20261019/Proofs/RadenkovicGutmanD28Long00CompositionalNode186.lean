/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode178
import Proofs.RadenkovicGutmanD28Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-52],[0]],[[0,0],[0]],[[-856,0],[0,0]],[[0,0],[0,0]],[[-5896,0],[0,0]],[[0,0],[0,0]],[[-22016,0],[0,0]],[[0,0],[0,0]],[[-48208,0],[0,0]],[[0,0],[0,0]],[[-62304,-52],[-52,0]],[[0,0],[0,0]],[[-44792,-388],[-388,0]],[[0,0],[0,0]],[[-14432,-948],[-948,0]],[[0,0],[0,0]],[[132,-800],[-800,0]],[[0,0],[0,0]],[[792,-104],[-104,0]],[[0,0],[0,0]],[[0,84],[84,-52]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
