/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode289
import Proofs.RadenkovicGutmanD33Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[4356,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[130680,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1799028,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[15063048,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[85717368,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[350945496,4356,0],[4356,0],[0]],[[0,0,0],[0,0],[0]],[[1067581548,95832,0],[95832,0],[0]],[[0,0,0],[0,0],[0]],[[2457315432,936540,0],[936540,0],[0]],[[0,0,0],[0,0],[0]],[[4318198632,5357880,0],[5357880,0],[0]],[[0,0,0],[0,0],[0]],[[5803420392,19911276,0],[19911276,0],[0]],[[0,0,0],[0,0],[0]],[[5935881996,50442480,1089],[50442480,2178],[1089]],[[0,0,0],[0,0],[0]],[[4564835352,88975656,15246],[88975656,30492],[15246]],[[0,0,0],[0,0],[0]],[[2582994744,109684080,88209],[109684080,176418],[88209]],[[0,0,0],[0,0],[0]],[[1037573064,93440556,272250],[93440556,544500],[272250]],[[0,0,0],[0,0],[0]],[[278387604,53448120,483516],[53448120,967032],[483516]],[[0,0,0],[0,0],[0]],[[44457336,19405980,498762],[19405980,997524],[498762]],[[0,0,0],[0,0],[0]],[[3175524,3998808,288585],[3998808,577170],[288585]],[[0,0,0],[0,0],[0]],[[0,352836,84942],[352836,169884],[84942]],[[0,0,0],[0,0],[0]],[[0,0,9801],[0,19602],[9801]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
