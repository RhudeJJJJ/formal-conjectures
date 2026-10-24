/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode253
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e254 : NestedArithmetic.Expr 3 := .times e253 e120
noncomputable def p254 : NestedHorner.Poly 3 := [[[4],[0],[0]],[[0,0],[0,0],[0]],[[152,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2624,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[27380,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[193560,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[983940,8,0],[8,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3722920,224,0],[224,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10701668,2776,0],[2776,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[23636432,20168,0],[20168,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[40290336,95760,0],[95760,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[52922588,313300,4],[313300,12,0],[4,0]],[[0,0,0],[0,0,0],[0,0]],[[53160236,725104,72],[725104,212,0],[72,0]],[[0,0,0],[0,0,0],[0,0]],[[40228152,1199004,548],[1199004,1588,0],[548,0]],[[0,0,0],[0,0,0],[0,0]],[[22358644,1412660,2300],[1412660,6580,0],[2300,0]],[[0,0,0],[0,0,0],[0,0]],[[8745904,1167652,5820],[1167652,16504,0],[5820,0]],[[0,0,0],[0,0,0],[0,0]],[[2228124,655412,9124],[655412,25784,4],[9124,4]],[[0,0,0],[0,0,0],[0,0]],[[310716,234860,8780],[234860,24900,32],[8780,32]],[[0,0,0],[0,0,0],[0,0]],[[10800,47268,4964],[47268,14244,92],[4964,92]],[[0,0,0],[0,0,0],[0,0]],[[-1620,3672,1488],[3672,4356,116],[1488,116]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,180],[-108,540,64],[180,64]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,12],[0,12]]]
theorem step254 : p254=NestedArithmetic.mul p253 p120 := by decide +kernel
#print axioms step254
theorem h254 : NestedArithmetic.compile e254=p254 := StagedExprCompile.compile_times e254 e253 e120 p253 p120 p254 rfl h253 h120 step254
#print axioms h254
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
