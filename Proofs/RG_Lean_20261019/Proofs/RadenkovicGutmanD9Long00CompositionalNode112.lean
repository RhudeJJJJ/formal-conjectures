/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode110
import Proofs.RadenkovicGutmanD9Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0,0]],[[0,0,729],[0,0,1674],[729,1674,232]],[[0,0,0],[0,0,0],[0,0,0]],[[6561,15066,17739],[15066,34308,9216],[17739,9216,4]],[[0,0,0],[0,0,0],[0,0]],[[303102,401598,116073],[401598,279912,16860],[116073,16860]],[[0,0,0],[0,0,0],[0,0]],[[5087151,3355398,353430],[3355398,930992,13352],[353430,13352]],[[0,0,0],[0,0,0],[0,0]],[[41951466,14334048,600876],[14334048,1682856,4626],[600876,4626]],[[0,0,0],[0,0,0],[0,0]],[[205816737,37327470,618456],[37327470,1835272,600],[618456,600]],[[0,0,0],[0,0,0],[0,0]],[[668630812,64573982,399073],[64573982,1257600,8],[399073,8]],[[0,0,0],[0,0],[0]],[[1533526178,77798380,162206],[77798380,543904],[162206]],[[0,0,0],[0,0],[0]],[[2586092546,67011984,40417],[67011984,144296],[40417]],[[0,0,0],[0,0],[0]],[[3293023904,41783286,5701],[41783286,21652],[5701]],[[0,0,0],[0,0],[0]],[[3221672072,18884466,368],[18884466,1480],[368]],[[0,0,0],[0,0],[0]],[[2447573808,6125518,4],[6125518,16],[4]],[[0,0],[0]],[[1451604414,1391528],[1391528]],[[0,0],[0]],[[672316365,211090],[211090]],[[0,0],[0]],[[242016420,19474],[19474]],[[0,0],[0]],[[66981754,880],[880]],[[0,0],[0]],[[13984854,8],[8]],[[0]],[[2134645]],[[0]],[[225978]],[[0]],[[15069]],[[0]],[[512]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
