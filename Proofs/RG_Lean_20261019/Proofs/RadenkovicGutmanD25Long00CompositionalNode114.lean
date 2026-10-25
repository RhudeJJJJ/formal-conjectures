/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,5625],[0,11250],[5625]],[[0,0,0],[0,0],[0]],[[0,202500,48750],[202500,97500],[48750]],[[0,0,0],[0,0],[0]],[[1822500,2295000,165625],[2295000,331250],[165625]],[[0,0,0],[0,0],[0]],[[25515000,11137500,286250],[11137500,572500],[286250]],[[0,0,0],[0,0],[0]],[[159772500,30675000,277500],[30675000,555000],[277500]],[[0,0,0],[0,0],[0]],[[595485000,53627500,156250],[53627500,312500],[156250]],[[0,0,0],[0,0],[0]],[[1482435000,62950000,50625],[62950000,101250],[50625]],[[0,0,0],[0,0],[0]],[[2619855000,51065000,8750],[51065000,17500],[8750]],[[0,0,0],[0,0],[0]],[[3406727500,28950000,625],[28950000,1250],[625]],[[0,0],[0]],[[3330705000,11427500],[11427500]],[[0,0],[0]],[[2478305000,3075000],[3075000]],[[0,0],[0]],[[1410305000,537500],[537500]],[[0,0],[0]],[[612707500,55000],[55000]],[[0,0],[0]],[[201415000,2500],[2500]],[[0]],[[49195000]],[[0]],[[8645000]],[[0]],[[1032500]],[[0]],[[75000]],[[0]],[[2500]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
