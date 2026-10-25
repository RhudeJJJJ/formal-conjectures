/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode035
import Proofs.RadenkovicGutmanD17Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-2601],[0,-5202],[-2601]],[[0,0,0],[0,0],[0]],[[0,-85833,-22542],[-85833,-45084],[-22542]],[[0,0,0],[0,0],[0]],[[-702270,-959769,-76585],[-959769,-153170],[-76585]],[[0,0,0],[0,0],[0]],[[-9597690,-4585563,-132362],[-4585563,-264724],[-132362]],[[0,0,0],[0,0],[0]],[[-58506894,-12412550,-128316],[-12412550,-256632],[-128316]],[[0,0,0],[0,0],[0]],[[-211783824,-21305947,-72250],[-21305947,-144500],[-72250]],[[0,0,0],[0,0],[0]],[[-511124244,-24546793,-23409],[-24546793,-46818],[-23409]],[[0,0,0],[0,0],[0]],[[-874547524,-19546804,-4046],[-19546804,-8092],[-4046]],[[0,0,0],[0,0],[0]],[[-1100051334,-10883451,-289],[-10883451,-578],[-289]],[[0,0],[0]],[[-1039809862,-4222001],[-4222001]],[[0,0],[0]],[[-747853392,-1117274],[-1117274]],[[0,0],[0]],[[-411356242,-192185],[-192185]],[[0,0],[0]],[[-172769402,-19363],[-19363]],[[0,0],[0]],[[-54918092,-867],[-867]],[[0]],[[-12973788]],[[0]],[[-2205648]],[[0]],[[-254898]],[[0]],[[-17918]],[[0]],[[-578]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
