/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode075
import Proofs.RadenkovicGutmanD17Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0]],[[0,0,2601],[0,5202,5202],[2601,5202]],[[0,0,0],[0,0,0],[0,0]],[[-23409,85833,45951],[85833,138720,13872],[45951,13872]],[[0,0,0],[0,0,0],[0,0]],[[296514,1381131,201433],[1381131,652562,12716],[201433,12716]],[[0,0,0],[0,0,0],[0,0]],[[8357013,7956459,413270],[7956459,1388356,4624],[413270,4624]],[[0,0,0],[0,0,0],[0,0]],[[64402494,24491594,475116],[24491594,1643832,578],[475116,578]],[[0,0,0],[0,0],[0]],[[267972071,46899787,328304],[46899787,1168716],[328304]],[[0,0,0],[0,0],[0]],[[718540700,60206503,139009],[60206503,509218],[139009]],[[0,0,0],[0,0],[0]],[[1348384410,53921620,35258],[53921620,132940],[35258]],[[0,0,0],[0,0],[0]],[[1854633802,34371059,4913],[34371059,19074],[4913]],[[0,0,0],[0,0],[0]],[[1922477130,15680273,289],[15680273,1156],[289]],[[0,0],[0]],[[1527035540,5079464],[5079464]],[[0,0],[0]],[[937669170,1140105],[1140105]],[[0,0],[0]],[[446198082,168487],[168487]],[[0,0],[0]],[[163949411,14739],[14739]],[[0,0],[0]],[[46030764,578],[578]],[[0]],[[9684390]],[[0]],[[1476790]],[[0]],[[154037]],[[0]],[[9826]],[[0]],[[289]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
