/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,2601],[0,5202],[2601]],[[0,0,0],[0,0],[0]],[[0,93636,22542],[93636,45084],[22542]],[[0,0,0],[0,0],[0]],[[842724,1061208,76585],[1061208,153170],[76585]],[[0,0,0],[0,0],[0]],[[11798136,5149980,132362],[5149980,264724],[132362]],[[0,0,0],[0,0],[0]],[[73878804,14184120,128316],[14184120,256632],[128316]],[[0,0,0],[0,0],[0]],[[275352264,24797356,72250],[24797356,144500],[72250]],[[0,0,0],[0,0],[0]],[[685477944,29108080,23409],[29108080,46818],[23409]],[[0,0,0],[0,0],[0]],[[1211420952,23612456,4046],[23612456,8092],[4046]],[[0,0,0],[0,0],[0]],[[1575270796,13386480,289],[13386480,578],[289]],[[0,0],[0]],[[1540117992,5284076],[5284076]],[[0,0],[0]],[[1145968232,1421880],[1421880]],[[0,0],[0]],[[652125032,248540],[248540]],[[0,0],[0]],[[283315948,25432],[25432]],[[0,0],[0]],[[93134296,1156],[1156]],[[0]],[[22747768]],[[0]],[[3997448]],[[0]],[[477428]],[[0]],[[34680]],[[0]],[[1156]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
