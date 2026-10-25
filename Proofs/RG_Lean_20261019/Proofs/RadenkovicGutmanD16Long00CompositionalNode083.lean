/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode070
import Proofs.RadenkovicGutmanD16Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,384],[0,384,848]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3456,12672],[3456,30240,17312],[12672,17312,4]],[[0,0,0],[0,0,0],[0,0]],[[-24624,427680,176208],[427680,527112,44488],[176208,44488]],[[0,0,0],[0,0,0],[0,0]],[[2411748,5717160,729028],[5717160,2309664,40448],[729028,40448]],[[0,0,0],[0,0,0],[0,0]],[[40771944,30805976,1458688],[30805976,4779336,14768],[1458688,14768]],[[0,0,0],[0,0,0],[0,0]],[[278297772,91684024,1654448],[91684024,5583376,1888],[1654448,1888]],[[0,0,0],[0,0,0],[0,0]],[[1094691512,172114784,1134368],[172114784,3944608,8],[1134368,8]],[[0,0,0],[0,0],[0]],[[2841146868,218154296,478552],[218154296,1716176],[478552]],[[0,0,0],[0,0],[0]],[[5219512368,193739928,121472],[193739928,449544],[121472]],[[0,0,0],[0,0],[0]],[[7073579480,122819664,17072],[122819664,65232],[17072]],[[0,0,0],[0,0],[0]],[[7253904712,55856672,1040],[55856672,4104],[1040]],[[0,0,0],[0,0],[0]],[[5716239744,18079032,4],[18079032,16],[4]],[[0,0],[0]],[[3489636928,4065672],[4065672]],[[0,0],[0]],[[1653799008,604600],[604600]],[[0,0],[0]],[[606145800,53728],[53728]],[[0,0],[0]],[[170034708,2216],[2216]],[[0,0],[0]],[[35812624,8],[8]],[[0]],[[5482488]],[[0]],[[576936]],[[0]],[[37556]],[[0]],[[1176]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
