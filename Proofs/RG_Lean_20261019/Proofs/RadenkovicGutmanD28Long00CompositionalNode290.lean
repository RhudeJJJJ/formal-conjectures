/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode289
import Proofs.RadenkovicGutmanD28Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[3136,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[94080,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1295168,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[10844288,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[61710208,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[252654976,3136,0],[3136,0],[0]],[[0,0,0],[0,0],[0]],[[768580288,68992,0],[68992,0],[0]],[[0,0,0],[0,0],[0]],[[1769086592,674240,0],[674240,0],[0]],[[0,0,0],[0,0],[0]],[[3108785792,3857280,0],[3857280,0],[0]],[[0,0,0],[0,0],[0]],[[4178036352,14334656,0],[14334656,0],[0]],[[0,0,0],[0,0],[0]],[[4273398976,36314880,784],[36314880,1568],[784]],[[0,0,0],[0,0],[0]],[[3286346112,64055936,10976],[64055936,21952],[10976]],[[0,0,0],[0,0],[0]],[[1859566464,78964480,63504],[78964480,127008],[63504]],[[0,0,0],[0,0],[0]],[[746976384,67270336,196000],[67270336,392000],[196000]],[[0,0,0],[0,0],[0]],[[200418624,38478720,348096],[38478720,696192],[348096]],[[0,0,0],[0,0],[0]],[[32006016,13970880,359072],[13970880,718144],[359072]],[[0,0,0],[0,0],[0]],[[2286144,2878848,207760],[2878848,415520],[207760]],[[0,0,0],[0,0],[0]],[[0,254016,61152],[254016,122304],[61152]],[[0,0,0],[0,0],[0]],[[0,0,7056],[0,14112],[7056]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
