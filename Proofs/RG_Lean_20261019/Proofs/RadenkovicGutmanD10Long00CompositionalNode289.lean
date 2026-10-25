/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[400],[0],[0]],[[0,0],[0,0],[0]],[[12000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[165200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1383200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7871200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[32226400,400,0],[400,0],[0]],[[0,0,0],[0,0],[0]],[[98033200,8800,0],[8800,0],[0]],[[0,0,0],[0,0],[0]],[[225648800,86000,0],[86000,0],[0]],[[0,0,0],[0,0],[0]],[[396528800,492000,0],[492000,0],[0]],[[0,0,0],[0,0],[0]],[[532912800,1828400,0],[1828400,0],[0]],[[0,0,0],[0,0],[0]],[[545076400,4632000,100],[4632000,200],[100]],[[0,0,0],[0,0],[0]],[[419176800,8170400,1400],[8170400,2800],[1400]],[[0,0,0],[0,0],[0]],[[237189600,10072000,8100],[10072000,16200],[8100]],[[0,0,0],[0,0],[0]],[[95277600,8580400,25000],[8580400,50000],[25000]],[[0,0,0],[0,0],[0]],[[25563600,4908000,44400],[4908000,88800],[44400]],[[0,0,0],[0,0],[0]],[[4082400,1782000,45800],[1782000,91600],[45800]],[[0,0,0],[0,0],[0]],[[291600,367200,26500],[367200,53000],[26500]],[[0,0,0],[0,0],[0]],[[0,32400,7800],[32400,15600],[7800]],[[0,0,0],[0,0],[0]],[[0,0,900],[0,1800],[900]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
