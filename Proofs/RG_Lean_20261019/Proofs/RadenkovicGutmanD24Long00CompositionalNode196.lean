/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode195
import Proofs.RadenkovicGutmanD24Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[96,0],[0]],[[0,0],[0]],[[1440,0],[0]],[[0,0],[0]],[[9024,0],[0]],[[0,0],[0]],[[30624,0],[0]],[[0,0],[0]],[[61056,0],[0]],[[0,0],[0]],[[72672,48],[48]],[[0,0],[0]],[[50112,336],[336]],[[0,0],[0]],[[18144,768],[768]],[[0,0],[0]],[[2592,624],[624]],[[0,0],[0]],[[0,144],[144]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
