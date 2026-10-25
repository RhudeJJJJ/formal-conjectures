/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode043
import Proofs.RadenkovicGutmanD7Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,441],[0,882,-420],[441,-420,100]],[[0,0,0],[0,0,0],[0,0]],[[0,16065,42],[16065,-7566,-20],[42,-20]],[[0,0,0],[0,0,0],[0,0]],[[121500,79515,-5375],[79515,-48250,2560],[-5375,2560]],[[0,0,0],[0,0,0],[0,0]],[[1004400,36891,-7438],[36891,-77286,3420],[-7438,3420]],[[0,0,0],[0,0,0],[0,0]],[[2578770,-558080,12976],[-558080,3812,1460],[12976,1460]],[[0,0,0],[0,0,0],[0,0]],[[-2636370,-1614437,43210],[-1614437,143900,200],[43210,200]],[[0,0,0],[0,0],[0]],[[-34144746,-1817049,47909],[-1817049,181198],[47909]],[[0,0,0],[0,0],[0]],[[-104063848,-255508,27526],[-255508,107922],[27526]],[[0,0,0],[0,0],[0]],[[-183439450,1810207,8749],[1810207,34758],[8749]],[[0,0,0],[0,0],[0]],[[-212657360,2526361,1460],[2526361,5830],[1460]],[[0,0,0],[0,0],[0]],[[-165363156,1805048,100],[1805048,400],[100]],[[0,0],[0]],[[-80283930,803705],[803705]],[[0,0],[0]],[[-14695286,231189],[231189]],[[0,0],[0]],[[10655230,41923],[41923]],[[0,0],[0]],[[10745574,4370],[4370]],[[0,0],[0]],[[5014740,200],[200]],[[0]],[[1489770]],[[0]],[[295428]],[[0]],[[38124]],[[0]],[[2910]],[[0]],[[100]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
