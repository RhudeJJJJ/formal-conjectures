/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode092
import Proofs.RadenkovicGutmanD22Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1584,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14256,-14256,0],[-14256,-13332,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-371844,-158004,0],[-158004,-43208,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3612708,-743688,0],[-743688,-68948,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19048128,-1963500,0],[-1963500,-57992,0],[0,0]],[[0,0,0],[0,0],[0]],[[-63269492,-3235496,0],[-3235496,-24464],[0]],[[0,0,0],[0,0],[0]],[[-143002332,-3487836,0],[-3487836,-3256],[0]],[[0,0,0],[0,0],[0]],[[-229876152,-2487056,0],[-2487056,1100],[0]],[[0,0,0],[0,0],[0]],[[-269528512,-1139336,0],[-1139336,440],[0]],[[0,0,0],[0,0],[0]],[[-233174348,-294976,0],[-294976,44],[0]],[[0,0],[0]],[[-148580344,-15356],[-15356]],[[0,0],[0]],[[-68310968,16280],[16280]],[[0,0],[0]],[[-21288080,5588],[5588]],[[0,0],[0]],[[-3569676,792],[792]],[[0,0],[0]],[[230164,44],[44]],[[0]],[[316008]],[[0]],[[90288]],[[0]],[[13948]],[[0]],[[1188]],[[0]],[[44]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
