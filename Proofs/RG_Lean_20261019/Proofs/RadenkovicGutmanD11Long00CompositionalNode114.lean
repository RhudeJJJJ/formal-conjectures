/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,1089],[0,2178],[1089]],[[0,0,0],[0,0],[0]],[[0,39204,9438],[39204,18876],[9438]],[[0,0,0],[0,0],[0]],[[352836,444312,32065],[444312,64130],[32065]],[[0,0,0],[0,0],[0]],[[4939704,2156220,55418],[2156220,110836],[55418]],[[0,0,0],[0,0],[0]],[[30931956,5938680,53724],[5938680,107448],[53724]],[[0,0,0],[0,0],[0]],[[115285896,10382284,30250],[10382284,60500],[30250]],[[0,0,0],[0,0],[0]],[[286999416,12187120,9801],[12187120,19602],[9801]],[[0,0,0],[0,0],[0]],[[507203928,9886184,1694],[9886184,3388],[1694]],[[0,0,0],[0,0],[0]],[[659542444,5604720,121],[5604720,242],[121]],[[0,0],[0]],[[644824488,2212364],[2212364]],[[0,0],[0]],[[479799848,595320],[595320]],[[0,0],[0]],[[273035048,104060],[104060]],[[0,0],[0]],[[118620172,10648],[10648]],[[0,0],[0]],[[38993944,484],[484]],[[0]],[[9524152]],[[0]],[[1673672]],[[0]],[[199892]],[[0]],[[14520]],[[0]],[[484]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
