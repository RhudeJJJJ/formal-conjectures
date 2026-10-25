/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,55296,0],[55296,9216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[912384,801792,0],[801792,79872,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[14902272,4939776,0],[4939776,271360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[108269568,17116160,0],[17116160,468992,0],[0,0]],[[0,0,0],[0,0],[0]],[[465146880,37306368,0],[37306368,454656],[0]],[[0,0,0],[0,0],[0]],[[1326212096,54289408,0],[54289408,256000],[0]],[[0,0,0],[0,0],[0]],[[2670360576,54595584,0],[54595584,82944],[0]],[[0,0,0],[0,0],[0]],[[3943542784,38653952,0],[38653952,14336],[0]],[[0,0,0],[0,0],[0]],[[4375489536,19384320,0],[19384320,1024],[0]],[[0,0],[0]],[[3702921216,6839296],[6839296]],[[0,0],[0]],[[2410260480,1658880],[1658880]],[[0,0],[0]],[[1209720832,263168],[263168]],[[0,0],[0]],[[466643968,24576],[24576]],[[0,0],[0]],[[136967168,1024],[1024]],[[0]],[[30013440]],[[0]],[[4751360]],[[0]],[[513024]],[[0]],[[33792]],[[0]],[[1024]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
