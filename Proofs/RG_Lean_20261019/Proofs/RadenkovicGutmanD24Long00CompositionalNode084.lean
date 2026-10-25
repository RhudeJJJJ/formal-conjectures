/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,31104,0],[31104,5184,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[513216,451008,0],[451008,44928,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8382528,2778624,0],[2778624,152640,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[60901632,9627840,0],[9627840,263808,0],[0,0]],[[0,0,0],[0,0],[0]],[[261645120,20984832,0],[20984832,255744],[0]],[[0,0,0],[0,0],[0]],[[745994304,30537792,0],[30537792,144000],[0]],[[0,0,0],[0,0],[0]],[[1502077824,30710016,0],[30710016,46656],[0]],[[0,0,0],[0,0],[0]],[[2218242816,21742848,0],[21742848,8064],[0]],[[0,0,0],[0,0],[0]],[[2461212864,10903680,0],[10903680,576],[0]],[[0,0],[0]],[[2082893184,3847104],[3847104]],[[0,0],[0]],[[1355771520,933120],[933120]],[[0,0],[0]],[[680467968,148032],[148032]],[[0,0],[0]],[[262487232,13824],[13824]],[[0,0],[0]],[[77044032,576],[576]],[[0]],[[16882560]],[[0]],[[2672640]],[[0]],[[288576]],[[0]],[[19008]],[[0]],[[576]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
