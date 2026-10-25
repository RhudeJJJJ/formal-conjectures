/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode289
import Proofs.RadenkovicGutmanD38Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[5776,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[173280,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2385488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[19973408,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[113660128,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[465349216,5776,0],[5776,0],[0]],[[0,0,0],[0,0],[0]],[[1415599408,127072,0],[127072,0],[0]],[[0,0,0],[0,0],[0]],[[3258368672,1241840,0],[1241840,0],[0]],[[0,0,0],[0,0],[0]],[[5725875872,7104480,0],[7104480,0],[0]],[[0,0,0],[0,0],[0]],[[7695260832,26402096,0],[26402096,0],[0]],[[0,0,0],[0,0],[0]],[[7870903216,66886080,1444],[66886080,2888],[1444]],[[0,0,0],[0,0],[0]],[[6052912992,117980576,20216],[117980576,40432],[20216]],[[0,0,0],[0,0],[0]],[[3425017824,145439680,116964],[145439680,233928],[116964]],[[0,0,0],[0,0],[0]],[[1375808544,123900976,361000],[123900976,722000],[361000]],[[0,0,0],[0,0],[0]],[[369138384,70871520,641136],[70871520,1282272],[641136]],[[0,0,0],[0,0],[0]],[[58949856,25732080,661352],[25732080,1322704],[661352]],[[0,0,0],[0,0],[0]],[[4210704,5302368,382660],[5302368,765320],[382660]],[[0,0,0],[0,0],[0]],[[0,467856,112632],[467856,225264],[112632]],[[0,0,0],[0,0],[0]],[[0,0,12996],[0,25992],[12996]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
