/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode240
import Proofs.RadenkovicGutmanD9Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[81,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2673,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[40581,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[375840,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2374110,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10834317,81,0],[81,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[36912267,1944,0],[1944,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[95690808,20817,0],[20817,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[190655370,131220,0],[131220,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[292906854,540999,0],[540999,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[346108059,1533330,0],[1533330,81,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[311940396,3057588,0],[3057588,1134,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[211229694,4318596,0],[4318596,6561,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[104905449,4294377,0],[4294377,20250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[36793845,2950992,0],[2950992,35964,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[8564292,1353915,0],[1353915,37098,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1178793,390744,0],[390744,21465,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[72171,63423,0],[63423,6318,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,4374,0],[4374,729,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
