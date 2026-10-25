/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode195
import Proofs.RadenkovicGutmanD25Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[100,0],[0]],[[0,0],[0]],[[1500,0],[0]],[[0,0],[0]],[[9400,0],[0]],[[0,0],[0]],[[31900,0],[0]],[[0,0],[0]],[[63600,0],[0]],[[0,0],[0]],[[75700,50],[50]],[[0,0],[0]],[[52200,350],[350]],[[0,0],[0]],[[18900,800],[800]],[[0,0],[0]],[[2700,650],[650]],[[0,0],[0]],[[0,150],[150]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
