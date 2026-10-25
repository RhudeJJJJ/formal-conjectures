/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode289
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[400,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[165200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1383200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7871200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[32226400,400,0],[400,0],[0]],[[0,0,0],[0,0],[0]],[[98033200,8800,0],[8800,0],[0]],[[0,0,0],[0,0],[0]],[[225648800,86000,0],[86000,0],[0]],[[0,0,0],[0,0],[0]],[[396528800,492000,0],[492000,0],[0]],[[0,0,0],[0,0],[0]],[[532912800,1828400,0],[1828400,0],[0]],[[0,0,0],[0,0],[0]],[[545076400,4632000,100],[4632000,200],[100]],[[0,0,0],[0,0],[0]],[[419176800,8170400,1400],[8170400,2800],[1400]],[[0,0,0],[0,0],[0]],[[237189600,10072000,8100],[10072000,16200],[8100]],[[0,0,0],[0,0],[0]],[[95277600,8580400,25000],[8580400,50000],[25000]],[[0,0,0],[0,0],[0]],[[25563600,4908000,44400],[4908000,88800],[44400]],[[0,0,0],[0,0],[0]],[[4082400,1782000,45800],[1782000,91600],[45800]],[[0,0,0],[0,0],[0]],[[291600,367200,26500],[367200,53000],[26500]],[[0,0,0],[0,0],[0]],[[0,32400,7800],[32400,15600],[7800]],[[0,0,0],[0,0],[0]],[[0,0,900],[0,1800],[900]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
