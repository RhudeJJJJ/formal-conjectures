/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,4374,0],[4374,729,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[72171,63423,0],[63423,6318,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1178793,390744,0],[390744,21465,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8564292,1353915,0],[1353915,37098,0],[0,0]],[[0,0,0],[0,0],[0]],[[36793845,2950992,0],[2950992,35964],[0]],[[0,0,0],[0,0],[0]],[[104905449,4294377,0],[4294377,20250],[0]],[[0,0,0],[0,0],[0]],[[211229694,4318596,0],[4318596,6561],[0]],[[0,0,0],[0,0],[0]],[[311940396,3057588,0],[3057588,1134],[0]],[[0,0,0],[0,0],[0]],[[346108059,1533330,0],[1533330,81],[0]],[[0,0],[0]],[[292906854,540999],[540999]],[[0,0],[0]],[[190655370,131220],[131220]],[[0,0],[0]],[[95690808,20817],[20817]],[[0,0],[0]],[[36912267,1944],[1944]],[[0,0],[0]],[[10834317,81],[81]],[[0]],[[2374110]],[[0]],[[375840]],[[0]],[[40581]],[[0]],[[2673]],[[0]],[[81]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
