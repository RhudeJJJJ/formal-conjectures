/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode221
import Proofs.RadenkovicGutmanD40Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[3200,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[99200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1411200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12211200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[71827200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[304044800,4800,0],[4800,0],[0]],[[0,0,0],[0,0],[0]],[[956508800,107200,0],[107200,0],[0]],[[0,0,0],[0,0],[0]],[[2277404800,1064000,0],[1064000,0],[0]],[[0,0,0],[0,0],[0]],[[4140364800,6185600,0],[6185600,0],[0]],[[0,0,0],[0,0],[0]],[[5756732800,23374400,0],[23374400,0],[0]],[[0,0,0],[0,0],[0]],[[6090249600,60254400,1600],[60254400,3200],[1600]],[[0,0,0],[0,0],[0]],[[4841785600,108217600,22400],[108217600,44800],[22400]],[[0,0,0],[0,0],[0]],[[2829753600,135899200,129600],[135899200,259200],[129600]],[[0,0,0],[0,0],[0]],[[1172505600,117956800,400000],[117956800,800000],[400000]],[[0,0,0],[0,0],[0]],[[323913600,68720000,710400],[68720000,1420800],[710400]],[[0,0,0],[0,0],[0]],[[53136000,25387200,732800],[25387200,1465600],[732800]],[[0,0,0],[0,0],[0]],[[3888000,5313600,424000],[5313600,848000],[424000]],[[0,0,0],[0,0],[0]],[[0,475200,124800],[475200,249600],[124800]],[[0,0,0],[0,0],[0]],[[0,0,14400],[0,28800],[14400]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
