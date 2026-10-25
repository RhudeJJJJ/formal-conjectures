/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode075
import Proofs.RadenkovicGutmanD7Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0]],[[0,0,441],[0,882,882],[441,882]],[[0,0,0],[0,0,0],[0,0]],[[-3969,14553,7791],[14553,23520,2352],[7791,2352]],[[0,0,0],[0,0,0],[0,0]],[[50274,234171,34153],[234171,110642,2156],[34153,2156]],[[0,0,0],[0,0,0],[0,0]],[[1416933,1349019,70070],[1349019,235396,784],[70070,784]],[[0,0,0],[0,0,0],[0,0]],[[10919454,4152554,80556],[4152554,278712,98],[80556,98]],[[0,0,0],[0,0],[0]],[[45434711,7951867,55664],[7951867,198156],[55664]],[[0,0,0],[0,0],[0]],[[121828700,10208023,23569],[10208023,86338],[23569]],[[0,0,0],[0,0],[0]],[[228618810,9142420,5978],[9142420,22540],[5978]],[[0,0,0],[0,0],[0]],[[314453482,5827619,833],[5827619,3234],[833]],[[0,0,0],[0,0],[0]],[[325956330,2658593,49],[2658593,196],[49]],[[0,0],[0]],[[258909140,861224],[861224]],[[0,0],[0]],[[158981970,193305],[193305]],[[0,0],[0]],[[75652962,28567],[28567]],[[0,0],[0]],[[27797651,2499],[2499]],[[0,0],[0]],[[7804524,98],[98]],[[0]],[[1641990]],[[0]],[[250390]],[[0]],[[26117]],[[0]],[[1666]],[[0]],[[49]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
