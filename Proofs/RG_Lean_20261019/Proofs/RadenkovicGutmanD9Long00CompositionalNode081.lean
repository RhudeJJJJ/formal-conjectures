/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode079
import Proofs.RadenkovicGutmanD9Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-4374,0],[-4374,-729,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-72171,-63423,0],[-63423,-6318,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1178793,-390744,0],[-390744,-21465,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8564292,-1353915,0],[-1353915,-37098,0],[0,0]],[[0,0,0],[0,0],[0]],[[-36793845,-2950992,0],[-2950992,-35964],[0]],[[0,0,0],[0,0],[0]],[[-104905449,-4294377,0],[-4294377,-20250],[0]],[[0,0,0],[0,0],[0]],[[-211229694,-4318596,0],[-4318596,-6561],[0]],[[0,0,0],[0,0],[0]],[[-311940396,-3057588,0],[-3057588,-1134],[0]],[[0,0,0],[0,0],[0]],[[-346108059,-1533330,0],[-1533330,-81],[0]],[[0,0],[0]],[[-292906854,-540999],[-540999]],[[0,0],[0]],[[-190655370,-131220],[-131220]],[[0,0],[0]],[[-95690808,-20817],[-20817]],[[0,0],[0]],[[-36912267,-1944],[-1944]],[[0,0],[0]],[[-10834317,-81],[-81]],[[0]],[[-2374110]],[[0]],[[-375840]],[[0]],[[-40581]],[[0]],[[-2673]],[[0]],[[-81]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
