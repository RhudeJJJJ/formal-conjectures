/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[3200],[0],[0]],[[0,0],[0,0],[0]],[[99200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1411200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12211200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[71827200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[304044800,4800,0],[4800,0],[0]],[[0,0,0],[0,0],[0]],[[956508800,107200,0],[107200,0],[0]],[[0,0,0],[0,0],[0]],[[2277404800,1064000,0],[1064000,0],[0]],[[0,0,0],[0,0],[0]],[[4140364800,6185600,0],[6185600,0],[0]],[[0,0,0],[0,0],[0]],[[5756732800,23374400,0],[23374400,0],[0]],[[0,0,0],[0,0],[0]],[[6090249600,60254400,1600],[60254400,3200],[1600]],[[0,0,0],[0,0],[0]],[[4841785600,108217600,22400],[108217600,44800],[22400]],[[0,0,0],[0,0],[0]],[[2829753600,135899200,129600],[135899200,259200],[129600]],[[0,0,0],[0,0],[0]],[[1172505600,117956800,400000],[117956800,800000],[400000]],[[0,0,0],[0,0],[0]],[[323913600,68720000,710400],[68720000,1420800],[710400]],[[0,0,0],[0,0],[0]],[[53136000,25387200,732800],[25387200,1465600],[732800]],[[0,0,0],[0,0],[0]],[[3888000,5313600,424000],[5313600,848000],[424000]],[[0,0,0],[0,0],[0]],[[0,475200,124800],[475200,249600],[124800]],[[0,0,0],[0,0],[0]],[[0,0,14400],[0,28800],[14400]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
