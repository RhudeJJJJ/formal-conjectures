/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode043
import Proofs.RadenkovicGutmanD27Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,6561],[0,13122,-8100],[6561,-8100,2500]],[[0,0,0],[0,0,0],[0,0]],[[0,222345,-16038],[222345,-169326,9900],[-16038,9900]],[[0,0,0],[0,0,0],[0,0]],[[1514700,605475,-114615],[605475,-770730,76800],[-114615,76800]],[[0,0,0],[0,0,0],[0,0]],[[8467200,-2520909,4482],[-2520909,-398086,91100],[4482,91100]],[[0,0,0],[0,0,0],[0,0]],[[-8957790,-13579920,709776],[-13579920,2626852,37300],[709776,37300]],[[0,0,0],[0,0,0],[0,0]],[[-214973970,-19591437,1465050],[-19591437,5917500,5000],[1465050,5000]],[[0,0,0],[0,0],[0]],[[-878096906,8095151,1412749],[8095151,5770398],[1412749]],[[0,0,0],[0,0],[0]],[[-1944730568,67593932,756406],[67593932,3082162],[756406]],[[0,0,0],[0,0],[0]],[[-2671708970,110605687,230229],[110605687,932758],[230229]],[[0,0,0],[0,0],[0]],[[-2216801120,102067361,37300],[102067361,150150],[37300]],[[0,0,0],[0,0],[0]],[[-724668116,60945928,2500],[60945928,10000],[2500]],[[0,0],[0]],[[707623670,24427905],[24427905]],[[0,0],[0]],[[1238916634,6546029],[6546029]],[[0,0],[0]],[[978995870,1127003],[1127003]],[[0,0],[0]],[[504974854,112850],[112850]],[[0,0],[0]],[[183113940,5000],[5000]],[[0]],[[47333370]],[[0]],[[8578228]],[[0]],[[1038524]],[[0]],[[75550]],[[0]],[[2500]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
