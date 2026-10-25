/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,10404],[0,20808],[10404]],[[0,0,0],[0,0],[0]],[[0,374544,90168],[374544,180336],[90168]],[[0,0,0],[0,0],[0]],[[3370896,4244832,306340],[4244832,612680],[306340]],[[0,0,0],[0,0],[0]],[[47192544,20599920,529448],[20599920,1058896],[529448]],[[0,0,0],[0,0],[0]],[[295515216,56736480,513264],[56736480,1026528],[513264]],[[0,0,0],[0,0],[0]],[[1101409056,99189424,289000],[99189424,578000],[289000]],[[0,0,0],[0,0],[0]],[[2741911776,116432320,93636],[116432320,187272],[93636]],[[0,0,0],[0,0],[0]],[[4845683808,94449824,16184],[94449824,32368],[16184]],[[0,0,0],[0,0],[0]],[[6301083184,53545920,1156],[53545920,2312],[1156]],[[0,0],[0]],[[6160471968,21136304],[21136304]],[[0,0],[0]],[[4583872928,5687520],[5687520]],[[0,0],[0]],[[2608500128,994160],[994160]],[[0,0],[0]],[[1133263792,101728],[101728]],[[0,0],[0]],[[372537184,4624],[4624]],[[0]],[[90991072]],[[0]],[[15989792]],[[0]],[[1909712]],[[0]],[[138720]],[[0]],[[4624]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
