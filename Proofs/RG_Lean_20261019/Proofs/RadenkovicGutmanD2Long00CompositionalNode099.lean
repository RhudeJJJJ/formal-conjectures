/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode049
import Proofs.RadenkovicGutmanD2Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .times e049 e051
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,96],[0,96,4]],[[0,0,0],[0,0,0],[0,0]],[[-324,216,540],[216,2232,368],[540,368]],[[0,0,0],[0,0,0],[0,0]],[[-1404,15120,3564],[15120,14880,496],[3564,496]],[[0,0,0],[0,0,0],[0,0]],[[90180,131832,9792],[131832,41288,296],[9792,296]],[[0,0,0],[0,0,0],[0,0]],[[1089996,534392,14744],[534392,62640,80],[14744,80]],[[0,0,0],[0,0,0],[0,0]],[[5929700,1285392,13432],[1285392,57280,8],[13432,8]],[[0,0,0],[0,0],[0]],[[19624644,2031632,7696],[2031632,32784],[7696]],[[0,0,0],[0,0],[0]],[[44216488,2223016,2784],[2223016,11784],[2784]],[[0,0,0],[0,0],[0]],[[71881864,1731288,616],[1731288,2576],[616]],[[0,0,0],[0,0],[0]],[[87236872,971816,76],[971816,312],[76]],[[0,0,0],[0,0],[0]],[[80697248,393432,4],[393432,16],[4]],[[0,0],[0]],[[57598000,113560],[113560]],[[0,0],[0]],[[31906720,22736],[22736]],[[0,0],[0]],[[13721748,2992],[2992]],[[0,0],[0]],[[4556900,232],[232]],[[0,0],[0]],[[1154664,8],[8]],[[0]],[[218600]],[[0]],[[29860]],[[0]],[[2772]],[[0]],[[156]],[[0]],[[4]]]
theorem step099 : p099=NestedArithmetic.mul p049 p051 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_times e099 e049 e051 p049 p051 p099 rfl h049 h051 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
