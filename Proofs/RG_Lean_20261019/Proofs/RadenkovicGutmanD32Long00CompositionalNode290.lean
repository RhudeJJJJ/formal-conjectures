/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode289
import Proofs.RadenkovicGutmanD32Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[4096,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[122880,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1691648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14163968,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[80601088,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[329998336,4096,0],[4096,0],[0]],[[0,0,0],[0,0],[0]],[[1003859968,90112,0],[90112,0],[0]],[[0,0,0],[0,0],[0]],[[2310643712,880640,0],[880640,0],[0]],[[0,0,0],[0,0],[0]],[[4060454912,5038080,0],[5038080,0],[0]],[[0,0,0],[0,0],[0]],[[5457027072,18722816,0],[18722816,0],[0]],[[0,0,0],[0,0],[0]],[[5581582336,47431680,1024],[47431680,2048],[1024]],[[0,0,0],[0,0],[0]],[[4292370432,83664896,14336],[83664896,28672],[14336]],[[0,0,0],[0,0],[0]],[[2428821504,103137280,82944],[103137280,165888],[82944]],[[0,0,0],[0,0],[0]],[[975642624,87863296,256000],[87863296,512000],[256000]],[[0,0,0],[0,0],[0]],[[261771264,50257920,454656],[50257920,909312],[454656]],[[0,0,0],[0,0],[0]],[[41803776,18247680,468992],[18247680,937984],[468992]],[[0,0,0],[0,0],[0]],[[2985984,3760128,271360],[3760128,542720],[271360]],[[0,0,0],[0,0],[0]],[[0,331776,79872],[331776,159744],[79872]],[[0,0,0],[0,0],[0]],[[0,0,9216],[0,18432],[9216]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
