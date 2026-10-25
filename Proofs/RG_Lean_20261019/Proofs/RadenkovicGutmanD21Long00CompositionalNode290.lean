/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode289
import Proofs.RadenkovicGutmanD21Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[1764,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[52920,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[728532,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6099912,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[34711992,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[142118424,1764,0],[1764,0],[0]],[[0,0,0],[0,0],[0]],[[432326412,38808,0],[38808,0],[0]],[[0,0,0],[0,0],[0]],[[995111208,379260,0],[379260,0],[0]],[[0,0,0],[0,0],[0]],[[1748692008,2169720,0],[2169720,0],[0]],[[0,0,0],[0,0],[0]],[[2350145448,8063244,0],[8063244,0],[0]],[[0,0,0],[0,0],[0]],[[2403786924,20427120,441],[20427120,882],[441]],[[0,0,0],[0,0],[0]],[[1848569688,36031464,6174],[36031464,12348],[6174]],[[0,0,0],[0,0],[0]],[[1046006136,44417520,35721],[44417520,71442],[35721]],[[0,0,0],[0,0],[0]],[[420174216,37839564,110250],[37839564,220500],[110250]],[[0,0,0],[0,0],[0]],[[112735476,21644280,195804],[21644280,391608],[195804]],[[0,0,0],[0,0],[0]],[[18003384,7858620,201978],[7858620,403956],[201978]],[[0,0,0],[0,0],[0]],[[1285956,1619352,116865],[1619352,233730],[116865]],[[0,0,0],[0,0],[0]],[[0,142884,34398],[142884,68796],[34398]],[[0,0,0],[0,0],[0]],[[0,0,3969],[0,7938],[3969]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
