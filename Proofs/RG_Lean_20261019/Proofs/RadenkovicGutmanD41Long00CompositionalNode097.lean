/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode051
import Proofs.RadenkovicGutmanD41Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5043],[0,-5043]],[[0,0,0],[0,0,0],[0,0]],[[0,45387,-75645],[45387,-226935,-22099],[-75645,-22099]],[[0,0,0],[0,0,0],[0,0]],[[680805,-1499985,-582159],[-1499985,-1672308,-27962],[-582159,-27962]],[[0,0,0],[0,0,0],[0,0]],[[-3891105,-18266976,-1783910],[-18266976,-4901919,-13079],[-1783910,-13079]],[[0,0,0],[0,0,0],[0,0]],[[-114820254,-85776797,-2855117],[-85776797,-7549248,-2255],[-2855117,-2255]],[[0,0,0],[0,0,0],[0,0]],[[-798733587,-225613652,-2623918],[-225613652,-6726296,-82],[-2623918,-82]],[[0,0,0],[0,0],[0]],[[-3024968971,-377247109,-1428891],[-377247109,-3577906],[-1428891]],[[0,0,0],[0,0],[0]],[[-7443363040,-425652242,-456494],[-425652242,-1124671],[-456494]],[[0,0,0],[0,0],[0]],[[-12861264744,-333827781,-79991],[-333827781,-195652],[-79991]],[[0,0,0],[0,0],[0]],[[-16275626951,-184078807,-6273],[-184078807,-15539],[-6273]],[[0,0,0],[0,0],[0]],[[-15457070438,-71130982,-82],[-71130982,-246],[-82]],[[0,0],[0]],[[-11167804188,-18883698],[-18883698]],[[0,0],[0]],[[-6174089468,-3294842],[-3294842]],[[0,0],[0]],[[-2609123273,-344728],[-344728]],[[0,0],[0]],[[-835955191,-17384],[-17384]],[[0,0],[0]],[[-199626540,-164],[-164]],[[0]],[[-34476900]],[[0]],[[-4087085]],[[0]],[[-301637]],[[0]],[[-11111]],[[0]],[[-82]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
