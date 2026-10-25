/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode217
import Proofs.RadenkovicGutmanD7Long00CompositionalNode186
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e266 : NestedArithmetic.Expr 3 := .times e217 e186
noncomputable def p266 : NestedHorner.Poly 3 := [[[140],[0],[0]],[[0,0],[0,0],[0]],[[4382,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[62902,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[548702,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3248952,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[13814192,210,0],[210,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[43510068,4753,0],[4753,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[103202918,47747,0],[47747,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[185475458,280315,0],[280315,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[251791708,1065596,0],[1065596,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[254705038,2744749,70],[2744749,280,0],[70,0]],[[0,0,0],[0,0,0],[0,0]],[[186338026,4866099,1001],[4866099,4102,0],[1001,0]],[[0,0,0],[0,0,0],[0,0]],[[92446396,5892936,5894],[5892936,24948,0],[5894,0]],[[0,0,0],[0,0,0],[0,0]],[[25979856,4695047,18361],[4695047,81382,0],[18361,0]],[[0,0,0],[0,0,0],[0,0]],[[513576,2213393,32270],[2213393,153580,0],[32270,0]],[[0,0,0],[0,0,0],[0,0]],[[-2420334,388430,31234],[388430,168448,70],[31234,70]],[[0,0,0],[0,0,0],[0,0]],[[-788130,-147483,14098],[-147483,101276,490],[14098,490]],[[0,0,0],[0,0,0],[0,0]],[[-85050,-87129,245],[-87129,26950,1120],[245,1120]],[[0,0,0],[0,0,0],[0,0]],[[0,-12663,-1932],[-12663,-84,910],[-1932,910]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-441],[0,-882,210],[-441,210]]]
theorem step266 : p266=NestedArithmetic.mul p217 p186 := by decide +kernel
#print axioms step266
theorem h266 : NestedArithmetic.compile e266=p266 := StagedExprCompile.compile_times e266 e217 e186 p217 p186 p266 rfl h217 h186 step266
#print axioms h266
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
