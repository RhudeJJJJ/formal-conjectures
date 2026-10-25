/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,3969],[0,7938],[3969]],[[0,0,0],[0,0],[0]],[[0,142884,34398],[142884,68796],[34398]],[[0,0,0],[0,0],[0]],[[1285956,1619352,116865],[1619352,233730],[116865]],[[0,0,0],[0,0],[0]],[[18003384,7858620,201978],[7858620,403956],[201978]],[[0,0,0],[0,0],[0]],[[112735476,21644280,195804],[21644280,391608],[195804]],[[0,0,0],[0,0],[0]],[[420174216,37839564,110250],[37839564,220500],[110250]],[[0,0,0],[0,0],[0]],[[1046006136,44417520,35721],[44417520,71442],[35721]],[[0,0,0],[0,0],[0]],[[1848569688,36031464,6174],[36031464,12348],[6174]],[[0,0,0],[0,0],[0]],[[2403786924,20427120,441],[20427120,882],[441]],[[0,0],[0]],[[2350145448,8063244],[8063244]],[[0,0],[0]],[[1748692008,2169720],[2169720]],[[0,0],[0]],[[995111208,379260],[379260]],[[0,0],[0]],[[432326412,38808],[38808]],[[0,0],[0]],[[142118424,1764],[1764]],[[0]],[[34711992]],[[0]],[[6099912]],[[0]],[[728532]],[[0]],[[52920]],[[0]],[[1764]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
