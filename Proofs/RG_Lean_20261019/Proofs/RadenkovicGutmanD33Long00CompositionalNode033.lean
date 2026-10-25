/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode030
import Proofs.RadenkovicGutmanD33Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0]],[[-297,297],[297]],[[0,0],[0]],[[99,792],[792]],[[0,0],[0]],[[5511,726],[726]],[[0,0],[0]],[[16962,264],[264]],[[0,0],[0]],[[24948,33],[33]],[[0]],[[20988]],[[0]],[[10527]],[[0]],[[3102]],[[0]],[[495]],[[0]],[[33]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
