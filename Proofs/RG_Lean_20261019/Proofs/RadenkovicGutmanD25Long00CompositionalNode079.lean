/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode033
import Proofs.RadenkovicGutmanD25Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1875],[0,1875]],[[0,0,0],[0,0,0],[0,0]],[[0,-16875,16875],[-16875,61875,8125],[16875,8125]],[[0,0,0],[0,0,0],[0,0]],[[-253125,185625,118125],[185625,423750,10000],[118125,10000]],[[0,0,0],[0,0,0],[0,0]],[[-1603125,2610000,326250],[2610000,1139375,4375],[326250,4375]],[[0,0,0],[0,0,0],[0,0]],[[877500,11811875,473125],[11811875,1606250,625],[473125,625]],[[0,0,0],[0,0],[0]],[[41289375,29246250,397500],[29246250,1312500],[397500]],[[0,0,0],[0,0],[0]],[[196268125,45944375,199375],[45944375,641250],[199375]],[[0,0,0],[0,0],[0]],[[519481250,48883750,58750],[48883750,184375],[58750]],[[0,0,0],[0,0],[0]],[[922087500,36330625,9375],[36330625,28750],[9375]],[[0,0,0],[0,0],[0]],[[1177671875,19066875,625],[19066875,1875],[625]],[[0,0],[0]],[[1120187500,7031250],[7031250]],[[0,0],[0]],[[807652500,1781250],[1781250]],[[0,0],[0]],[[444645000,295000],[295000]],[[0,0],[0]],[[186803125,28750],[28750]],[[0,0],[0]],[[59383125,1250],[1250]],[[0]],[[14028750]],[[0]],[[2385000]],[[0]],[[275625]],[[0]],[[19375]],[[0]],[[625]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
