/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode043
import Proofs.RadenkovicGutmanD9Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,243],[0,243,-126]],[[0,0,0],[0,0,0],[0,0]],[[0,2187,2187],[2187,9396,-1215],[2187,-1215]],[[0,0,0],[0,0,0],[0,0]],[[55404,93312,5103],[93312,26028,-4752],[5103,-4752]],[[0,0,0],[0,0,0],[0,0]],[[1301508,611388,-12150],[611388,-29520,-4977],[-12150,-4977]],[[0,0,0],[0,0,0],[0,0]],[[10735254,1735830,-61155],[1735830,-211644,-1935],[-61155,-1935]],[[0,0,0],[0,0,0],[0,0]],[[47746044,2358450,-99684],[2358450,-366768,-252],[-99684,-252]],[[0,0,0],[0,0],[0]],[[133770348,634680,-85797],[634680,-325188],[-85797]],[[0,0,0],[0,0],[0]],[[253606176,-3080250,-42786],[-3080250,-165312],[-42786]],[[0,0,0],[0,0],[0]],[[335267460,-5750235,-12393],[-5750235,-48564],[-12393]],[[0,0,0],[0,0],[0]],[[307611198,-5402115,-1935],[-5402115,-7668],[-1935]],[[0,0,0],[0,0],[0]],[[183108042,-3214287,-126],[-3214287,-504],[-126]],[[0,0],[0]],[[48861270,-1276830],[-1276830]],[[0,0],[0]],[[-24891264,-338751],[-338751]],[[0,0],[0]],[[-36566136,-57762],[-57762]],[[0,0],[0]],[[-22164696,-5733],[-5733]],[[0,0],[0]],[[-8604036,-252],[-252]],[[0]],[[-2300940]],[[0]],[[-424674]],[[0]],[[-51930]],[[0]],[[-3798]],[[0]],[[-126]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
