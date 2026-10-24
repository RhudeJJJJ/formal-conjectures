/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode049
import Proofs.RadenkovicGutmanD2Long00CompositionalNode059
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .times e049 e059
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,12],[0,12,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-108,180],[-108,540,64],[180,64,0]],[[0,0,0],[0,0,0],[0,0]],[[-1620,3672,1488],[3672,4356,116],[1488,116]],[[0,0,0],[0,0,0],[0,0]],[[10800,47268,4964],[47268,14244,92],[4964,92]],[[0,0,0],[0,0,0],[0,0]],[[310716,234860,8780],[234860,24900,32],[8780,32]],[[0,0,0],[0,0,0],[0,0]],[[2228124,655412,9124],[655412,25784,4],[9124,4]],[[0,0,0],[0,0,0],[0,0]],[[8745904,1167652,5820],[1167652,16504,0],[5820,0]],[[0,0,0],[0,0],[0]],[[22358644,1412660,2300],[1412660,6580],[2300]],[[0,0,0],[0,0],[0]],[[40228152,1199004,548],[1199004,1588],[548]],[[0,0,0],[0,0],[0]],[[53160236,725104,72],[725104,212],[72]],[[0,0,0],[0,0],[0]],[[52922588,313300,4],[313300,12],[4]],[[0,0,0],[0,0],[0]],[[40290336,95760,0],[95760,0],[0]],[[0,0],[0]],[[23636432,20168],[20168]],[[0,0],[0]],[[10701668,2776],[2776]],[[0,0],[0]],[[3722920,224],[224]],[[0,0],[0]],[[983940,8],[8]],[[0,0],[0]],[[193560,0],[0]],[[0]],[[27380]],[[0]],[[2624]],[[0]],[[152]],[[0]],[[4]],[[0]],[[0]]]
theorem step070 : p070=NestedArithmetic.mul p049 p059 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_times e070 e049 e059 p049 p059 p070 rfl h049 h059 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
