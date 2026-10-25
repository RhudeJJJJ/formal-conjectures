/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[7396],[0],[0]],[[0,0],[0,0],[0]],[[221880,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3054548,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[25575368,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[145538488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[595866136,7396,0],[7396,0],[0]],[[0,0,0],[0,0],[0]],[[1812633868,162712,0],[162712,0],[0]],[[0,0,0],[0,0],[0]],[[4172246312,1590140,0],[1590140,0],[0]],[[0,0,0],[0,0],[0]],[[7331817512,9097080,0],[9097080,0],[0]],[[0,0,0],[0,0],[0]],[[9853557672,33807116,0],[33807116,0],[0]],[[0,0,0],[0,0],[0]],[[10078462636,85645680,1849],[85645680,3698],[1849]],[[0,0,0],[0,0],[0]],[[7750579032,151070696,25886],[151070696,51772],[25886]],[[0,0,0],[0,0],[0]],[[4385635704,186231280,149769],[186231280,299538],[149769]],[[0,0,0],[0,0],[0]],[[1761682824,158651596,462250],[158651596,924500],[462250]],[[0,0,0],[0,0],[0]],[[472670964,90748920,820956],[90748920,1641912],[820956]],[[0,0,0],[0,0],[0]],[[75483576,32949180,846842],[32949180,1693684],[846842]],[[0,0,0],[0,0],[0]],[[5391684,6789528,489985],[6789528,979970],[489985]],[[0,0,0],[0,0],[0]],[[0,599076,144222],[599076,288444],[144222]],[[0,0,0],[0,0],[0]],[[0,0,16641],[0,33282],[16641]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
