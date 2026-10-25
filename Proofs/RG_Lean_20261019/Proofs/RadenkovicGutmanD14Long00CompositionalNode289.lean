/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[784],[0],[0]],[[0,0],[0,0],[0]],[[23520,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[323792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2711072,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[15427552,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[63163744,784,0],[784,0],[0]],[[0,0,0],[0,0],[0]],[[192145072,17248,0],[17248,0],[0]],[[0,0,0],[0,0],[0]],[[442271648,168560,0],[168560,0],[0]],[[0,0,0],[0,0],[0]],[[777196448,964320,0],[964320,0],[0]],[[0,0,0],[0,0],[0]],[[1044509088,3583664,0],[3583664,0],[0]],[[0,0,0],[0,0],[0]],[[1068349744,9078720,196],[9078720,392],[196]],[[0,0,0],[0,0],[0]],[[821586528,16013984,2744],[16013984,5488],[2744]],[[0,0,0],[0,0],[0]],[[464891616,19741120,15876],[19741120,31752],[15876]],[[0,0,0],[0,0],[0]],[[186744096,16817584,49000],[16817584,98000],[49000]],[[0,0,0],[0,0],[0]],[[50104656,9619680,87024],[9619680,174048],[87024]],[[0,0,0],[0,0],[0]],[[8001504,3492720,89768],[3492720,179536],[89768]],[[0,0,0],[0,0],[0]],[[571536,719712,51940],[719712,103880],[51940]],[[0,0,0],[0,0],[0]],[[0,63504,15288],[63504,30576],[15288]],[[0,0,0],[0,0],[0]],[[0,0,1764],[0,3528],[1764]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
