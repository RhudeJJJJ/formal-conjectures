/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[578],[0],[0]],[[0,0],[0,0],[0]],[[17918,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[254898,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2205648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12973788,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[54918092,867,0],[867,0],[0]],[[0,0,0],[0,0],[0]],[[172769402,19363,0],[19363,0],[0]],[[0,0,0],[0,0],[0]],[[411356242,192185,0],[192185,0],[0]],[[0,0,0],[0,0],[0]],[[747853392,1117274,0],[1117274,0],[0]],[[0,0,0],[0,0],[0]],[[1039809862,4222001,0],[4222001,0],[0]],[[0,0,0],[0,0],[0]],[[1100051334,10883451,289],[10883451,578],[289]],[[0,0,0],[0,0],[0]],[[874547524,19546804,4046],[19546804,8092],[4046]],[[0,0,0],[0,0],[0]],[[511124244,24546793,23409],[24546793,46818],[23409]],[[0,0,0],[0,0],[0]],[[211783824,21305947,72250],[21305947,144500],[72250]],[[0,0,0],[0,0],[0]],[[58506894,12412550,128316],[12412550,256632],[128316]],[[0,0,0],[0,0],[0]],[[9597690,4585563,132362],[4585563,264724],[132362]],[[0,0,0],[0,0],[0]],[[702270,959769,76585],[959769,153170],[76585]],[[0,0,0],[0,0],[0]],[[0,85833,22542],[85833,45084],[22542]],[[0,0,0],[0,0],[0]],[[0,0,2601],[0,5202],[2601]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
