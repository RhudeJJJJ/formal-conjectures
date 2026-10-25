/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode289
import Proofs.RadenkovicGutmanD23Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[2116,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[63480,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[873908,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7317128,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[41638648,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[170477656,2116,0],[2116,0],[0]],[[0,0,0],[0,0],[0]],[[518595628,46552,0],[46552,0],[0]],[[0,0,0],[0,0],[0]],[[1193682152,454940,0],[454940,0],[0]],[[0,0,0],[0,0],[0]],[[2097637352,2602680,0],[2602680,0],[0]],[[0,0,0],[0,0],[0]],[[2819108712,9672236,0],[9672236,0],[0]],[[0,0,0],[0,0],[0]],[[2883454156,24503280,529],[24503280,1058],[529]],[[0,0,0],[0,0],[0]],[[2217445272,43221416,7406],[43221416,14812],[7406]],[[0,0,0],[0,0],[0]],[[1254732984,53280880,42849],[53280880,85698],[42849]],[[0,0,0],[0,0],[0]],[[504018504,45390316,132250],[45390316,264500],[132250]],[[0,0,0],[0,0],[0]],[[135231444,25963320,234876],[25963320,469752],[234876]],[[0,0,0],[0,0],[0]],[[21595896,9426780,242282],[9426780,484564],[242282]],[[0,0,0],[0,0],[0]],[[1542564,1942488,140185],[1942488,280370],[140185]],[[0,0,0],[0,0],[0]],[[0,171396,41262],[171396,82524],[41262]],[[0,0,0],[0,0],[0]],[[0,0,4761],[0,9522],[4761]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
