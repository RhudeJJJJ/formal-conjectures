/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode193
import Proofs.RadenkovicGutmanD25Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[155,0],[0,0]],[[0,0],[0,0]],[[2063,0],[0,0]],[[0,0],[0,0]],[[12388,0],[0,0]],[[0,0],[0,0]],[[41147,0],[0,0]],[[0,0],[0,0]],[[81012,2],[2,0]],[[0,0],[0,0]],[[95628,91],[91,0]],[[0,0],[0,0]],[[65384,594],[594,0]],[[0,0],[0,0]],[[23081,1398],[1398,0]],[[0,0],[0,0]],[[2757,1268],[1268,0]],[[0,0],[0,0]],[[-225,375],[375,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
