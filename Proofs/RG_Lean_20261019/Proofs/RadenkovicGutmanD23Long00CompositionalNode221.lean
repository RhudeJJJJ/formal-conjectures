/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[1058],[0],[0]],[[0,0],[0,0],[0]],[[32798,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[466578,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4037328,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[23747868,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[100524812,1587,0],[1587,0],[0]],[[0,0,0],[0,0],[0]],[[316245722,35443,0],[35443,0],[0]],[[0,0,0],[0,0],[0]],[[752966962,351785,0],[351785,0],[0]],[[0,0,0],[0,0],[0]],[[1368908112,2045114,0],[2045114,0],[0]],[[0,0,0],[0,0],[0]],[[1903319782,7728161,0],[7728161,0],[0]],[[0,0,0],[0,0],[0]],[[2013588774,19921611,529],[19921611,1058],[529]],[[0,0,0],[0,0],[0]],[[1600815364,35779444,7406],[35779444,14812],[7406]],[[0,0,0],[0,0],[0]],[[935587284,44931673,42849],[44931673,85698],[42849]],[[0,0,0],[0,0],[0]],[[387659664,38999467,132250],[38999467,264500],[132250]],[[0,0,0],[0,0],[0]],[[107093934,22720550,234876],[22720550,469752],[234876]],[[0,0,0],[0,0],[0]],[[17568090,8393643,242282],[8393643,484564],[242282]],[[0,0,0],[0,0],[0]],[[1285470,1756809,140185],[1756809,280370],[140185]],[[0,0,0],[0,0],[0]],[[0,157113,41262],[157113,82524],[41262]],[[0,0,0],[0,0],[0]],[[0,0,4761],[0,9522],[4761]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
