/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode032
import Proofs.RadenkovicGutmanD3Long00StagedUNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .times e032 e052
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,162],[0,162]],[[0,0,0],[0,0,0],[0,0]],[[-729,0,729],[0,2916,432],[729,432]],[[0,0,0],[0,0,0],[0,0]],[[-12636,13122,3888],[13122,15552,396],[3888,396]],[[0,0,0],[0,0,0],[0,0]],[[-38637,104976,8748],[104976,34992,144],[8748,144]],[[0,0,0],[0,0,0],[0,0]],[[183600,376164,10800],[376164,43200,18],[10800,18]],[[0,0,0],[0,0],[0]],[[1749807,797040,7974],[797040,31896],[7974]],[[0,0,0],[0,0],[0]],[[6459336,1110510,3600],[1110510,14400],[3600]],[[0,0,0],[0,0],[0]],[[14756166,1070496,972],[1070496,3888],[972]],[[0,0,0],[0,0],[0]],[[23499108,731448,144],[731448,576],[144]],[[0,0,0],[0,0],[0]],[[27487908,356832,9],[356832,36],[9]],[[0,0],[0]],[[24265188,123390],[123390]],[[0,0],[0]],[[16390368,29520],[29520]],[[0,0],[0]],[[8515080,4644],[4644]],[[0,0],[0]],[[3395439,432],[432]],[[0,0],[0]],[[1029456,18],[18]],[[0]],[[232902]],[[0]],[[38052]],[[0]],[[4239]],[[0]],[[288]],[[0]],[[9]]]
theorem step073 : p073=NestedArithmetic.mul p032 p052 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_times e073 e032 e052 p032 p052 p073 rfl h032 h052 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
