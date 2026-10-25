/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode193
import Proofs.RadenkovicGutmanD26Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[160,0],[0,0]],[[0,0],[0,0]],[[2138,0],[0,0]],[[0,0],[0,0]],[[12858,0],[0,0]],[[0,0],[0,0]],[[42742,0],[0,0]],[[0,0],[0,0]],[[84192,2],[2,0]],[[0,0],[0,0]],[[99412,94],[94,0]],[[0,0],[0,0]],[[67986,616],[616,0]],[[0,0],[0,0]],[[24004,1452],[1452,0]],[[0,0],[0,0]],[[2868,1318],[1318,0]],[[0,0],[0,0]],[[-234,390],[390,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
