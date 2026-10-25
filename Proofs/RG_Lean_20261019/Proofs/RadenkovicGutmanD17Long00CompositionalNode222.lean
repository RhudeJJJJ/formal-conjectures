/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode221
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[578,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[17918,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[254898,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2205648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12973788,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[54918092,867,0],[867,0],[0]],[[0,0,0],[0,0],[0]],[[172769402,19363,0],[19363,0],[0]],[[0,0,0],[0,0],[0]],[[411356242,192185,0],[192185,0],[0]],[[0,0,0],[0,0],[0]],[[747853392,1117274,0],[1117274,0],[0]],[[0,0,0],[0,0],[0]],[[1039809862,4222001,0],[4222001,0],[0]],[[0,0,0],[0,0],[0]],[[1100051334,10883451,289],[10883451,578],[289]],[[0,0,0],[0,0],[0]],[[874547524,19546804,4046],[19546804,8092],[4046]],[[0,0,0],[0,0],[0]],[[511124244,24546793,23409],[24546793,46818],[23409]],[[0,0,0],[0,0],[0]],[[211783824,21305947,72250],[21305947,144500],[72250]],[[0,0,0],[0,0],[0]],[[58506894,12412550,128316],[12412550,256632],[128316]],[[0,0,0],[0,0],[0]],[[9597690,4585563,132362],[4585563,264724],[132362]],[[0,0,0],[0,0],[0]],[[702270,959769,76585],[959769,153170],[76585]],[[0,0,0],[0,0],[0]],[[0,85833,22542],[85833,45084],[22542]],[[0,0,0],[0,0],[0]],[[0,0,2601],[0,5202],[2601]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
