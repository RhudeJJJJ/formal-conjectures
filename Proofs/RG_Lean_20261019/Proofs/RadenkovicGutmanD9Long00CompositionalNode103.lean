/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-486],[0,-486,126]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-5832],[0,-20331,108],[-5832,108]],[[0,0,0],[0,0,0],[0,0]],[[-22599,-165969,-33534],[-165969,-108000,3222],[-33534,3222]],[[0,0,0],[0,0,0],[0,0]],[[-1494693,-1505628,-76464],[-1505628,-216207,4122],[-76464,4122]],[[0,0,0],[0,0,0],[0,0]],[[-16406388,-5982579,-83754],[-5982579,-177732,1728],[-83754,1728]],[[0,0,0],[0,0,0],[0,0]],[[-87442767,-13667526,-37386],[-13667526,6552,234],[-37386,234]],[[0,0,0],[0,0],[0]],[[-285245559,-19809405,8010],[-19809405,123282],[8010]],[[0,0,0],[0,0],[0]],[[-629426880,-18906264,16308],[-18906264,96705],[16308]],[[0,0,0],[0,0],[0]],[[-990531180,-11829546,7218],[-11829546,34992],[7218]],[[0,0,0],[0,0],[0]],[[-1145148741,-4527828,1422],[-4527828,6273],[1422]],[[0,0,0],[0,0],[0]],[[-987517296,-745047,108],[-745047,450],[108]],[[0,0],[0]],[[-637632882,179244],[179244]],[[0,0],[0]],[[-305638524,134469],[134469]],[[0,0],[0]],[[-105746193,33930],[33930]],[[0,0],[0]],[[-24517791,4221],[4221]],[[0,0],[0]],[[-2894184,216],[216]],[[0]],[[227880]],[[0]],[[162549]],[[0]],[[30357]],[[0]],[[2799]],[[0]],[[108]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
