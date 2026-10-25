/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode033
import Proofs.RadenkovicGutmanD37Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,24642],[0,24642]],[[0,0,0],[0,0,0],[0,0]],[[-110889,0,110889],[0,443556,65712],[110889,65712]],[[0,0,0],[0,0,0],[0,0]],[[-1922076,1996002,591408],[1996002,2365632,60236],[591408,60236]],[[0,0,0],[0,0,0],[0,0]],[[-5877117,15968016,1330668],[15968016,5322672,21904],[1330668,21904]],[[0,0,0],[0,0,0],[0,0]],[[27927600,57218724,1642800],[57218724,6571200,2738],[1642800,2738]],[[0,0,0],[0,0],[0]],[[266165087,121238640,1212934],[121238640,4851736],[1212934]],[[0,0,0],[0,0],[0]],[[982536776,168920910,547600],[168920910,2190400],[547600]],[[0,0,0],[0,0],[0]],[[2244576806,162834336,147852],[162834336,591408],[147852]],[[0,0,0],[0,0],[0]],[[3574475428,111261368,21904],[111261368,87616],[21904]],[[0,0,0],[0,0],[0]],[[4181216228,54278112,1369],[54278112,5476],[1369]],[[0,0],[0]],[[3691004708,18768990],[18768990]],[[0,0],[0]],[[2493157088,4490320],[4490320]],[[0,0],[0]],[[1295238280,706404],[706404]],[[0,0],[0]],[[516483999,65712],[65712]],[[0,0],[0]],[[156591696,2738],[2738]],[[0]],[[35426982]],[[0]],[[5788132]],[[0]],[[644799]],[[0]],[[43808]],[[0]],[[1369]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
