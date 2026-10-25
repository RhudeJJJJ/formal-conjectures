/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,28566,0],[28566,4761,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[471339,414207,0],[414207,41262,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7698537,2551896,0],[2551896,140185,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[55932228,8842235,0],[8842235,242282,0],[0,0]],[[0,0,0],[0,0],[0]],[[240295605,19272528,0],[19272528,234876],[0]],[[0,0,0],[0,0],[0]],[[685123241,28045993,0],[28045993,132250],[0]],[[0,0,0],[0,0],[0]],[[1379512446,28204164,0],[28204164,42849],[0]],[[0,0,0],[0,0],[0]],[[2037240364,19968692,0],[19968692,7406],[0]],[[0,0,0],[0,0],[0]],[[2260384731,10013970,0],[10013970,529],[0]],[[0,0],[0]],[[1912934886,3533191],[3533191]],[[0,0],[0]],[[1245144330,856980],[856980]],[[0,0],[0]],[[624943672,135953],[135953]],[[0,0],[0]],[[241069003,12696],[12696]],[[0,0],[0]],[[70757453,529],[529]],[[0]],[[15504990]],[[0]],[[2454560]],[[0]],[[265029]],[[0]],[[17457]],[[0]],[[529]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
