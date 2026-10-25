/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode195
import Proofs.RadenkovicGutmanD44Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[176,0],[0]],[[0,0],[0]],[[2640,0],[0]],[[0,0],[0]],[[16544,0],[0]],[[0,0],[0]],[[56144,0],[0]],[[0,0],[0]],[[111936,0],[0]],[[0,0],[0]],[[133232,88],[88]],[[0,0],[0]],[[91872,616],[616]],[[0,0],[0]],[[33264,1408],[1408]],[[0,0],[0]],[[4752,1144],[1144]],[[0,0],[0]],[[0,264],[264]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
