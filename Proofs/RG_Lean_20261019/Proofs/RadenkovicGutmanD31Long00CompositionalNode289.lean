/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[3844],[0],[0]],[[0,0],[0,0],[0]],[[115320,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1587572,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[13292552,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[75642232,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[309695704,3844,0],[3844,0],[0]],[[0,0,0],[0,0],[0]],[[942099052,84568,0],[84568,0],[0]],[[0,0,0],[0,0],[0]],[[2168484968,826460,0],[826460,0],[0]],[[0,0,0],[0,0],[0]],[[3810641768,4728120,0],[4728120,0],[0]],[[0,0,0],[0,0],[0]],[[5121292008,17570924,0],[17570924,0],[0]],[[0,0,0],[0,0],[0]],[[5238184204,44513520,961],[44513520,1922],[961]],[[0,0,0],[0,0],[0]],[[4028289048,78517544,13454],[78517544,26908],[13454]],[[0,0,0],[0,0],[0]],[[2279392056,96791920,77841],[96791920,155682],[77841]],[[0,0,0],[0,0],[0]],[[915617736,82457644,240250],[82457644,480500],[240250]],[[0,0,0],[0,0],[0]],[[245666196,47165880,426684],[47165880,853368],[426684]],[[0,0,0],[0,0],[0]],[[39231864,17125020,440138],[17125020,880276],[440138]],[[0,0,0],[0,0],[0]],[[2802276,3528792,254665],[3528792,509330],[254665]],[[0,0,0],[0,0],[0]],[[0,311364,74958],[311364,149916],[74958]],[[0,0,0],[0,0],[0]],[[0,0,8649],[0,17298],[8649]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
