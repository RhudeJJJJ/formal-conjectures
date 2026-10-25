/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode035
import Proofs.RadenkovicGutmanD7Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-441],[0,-882,210],[-441,210]],[[0,0,0],[0,0,0],[0,0]],[[0,-12663,-1932],[-12663,-84,910],[-1932,910]],[[0,0,0],[0,0,0],[0,0]],[[-85050,-87129,245],[-87129,26950,1120],[245,1120]],[[0,0,0],[0,0,0],[0,0]],[[-788130,-147483,14098],[-147483,101276,490],[14098,490]],[[0,0,0],[0,0,0],[0,0]],[[-2420334,388430,31234],[388430,168448,70],[31234,70]],[[0,0,0],[0,0],[0]],[[513576,2213393,32270],[2213393,153580],[32270]],[[0,0,0],[0,0],[0]],[[25979856,4695047,18361],[4695047,81382],[18361]],[[0,0,0],[0,0],[0]],[[92446396,5892936,5894],[5892936,24948],[5894]],[[0,0,0],[0,0],[0]],[[186338026,4866099,1001],[4866099,4102],[1001]],[[0,0,0],[0,0],[0]],[[254705038,2744749,70],[2744749,280],[70]],[[0,0],[0]],[[251791708,1065596],[1065596]],[[0,0],[0]],[[185475458,280315],[280315]],[[0,0],[0]],[[103202918,47747],[47747]],[[0,0],[0]],[[43510068,4753],[4753]],[[0,0],[0]],[[13814192,210],[210]],[[0]],[[3248952]],[[0]],[[548702]],[[0]],[[62902]],[[0]],[[4382]],[[0]],[[140]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
