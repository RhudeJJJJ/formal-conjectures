/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[4096],[0],[0]],[[0,0],[0,0],[0]],[[122880,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1691648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14163968,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[80601088,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[329998336,4096,0],[4096,0],[0]],[[0,0,0],[0,0],[0]],[[1003859968,90112,0],[90112,0],[0]],[[0,0,0],[0,0],[0]],[[2310643712,880640,0],[880640,0],[0]],[[0,0,0],[0,0],[0]],[[4060454912,5038080,0],[5038080,0],[0]],[[0,0,0],[0,0],[0]],[[5457027072,18722816,0],[18722816,0],[0]],[[0,0,0],[0,0],[0]],[[5581582336,47431680,1024],[47431680,2048],[1024]],[[0,0,0],[0,0],[0]],[[4292370432,83664896,14336],[83664896,28672],[14336]],[[0,0,0],[0,0],[0]],[[2428821504,103137280,82944],[103137280,165888],[82944]],[[0,0,0],[0,0],[0]],[[975642624,87863296,256000],[87863296,512000],[256000]],[[0,0,0],[0,0],[0]],[[261771264,50257920,454656],[50257920,909312],[454656]],[[0,0,0],[0,0],[0]],[[41803776,18247680,468992],[18247680,937984],[468992]],[[0,0,0],[0,0],[0]],[[2985984,3760128,271360],[3760128,542720],[271360]],[[0,0,0],[0,0],[0]],[[0,331776,79872],[331776,159744],[79872]],[[0,0,0],[0,0],[0]],[[0,0,9216],[0,18432],[9216]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
