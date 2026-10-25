/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode049
import Proofs.RadenkovicGutmanD9Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,9]],[[0,0],[0,0]],[[-81,135],[135,2]],[[0,0],[0]],[[1017,468],[468]],[[0,0],[0]],[[8625,534],[534]],[[0,0],[0]],[[24812,242],[242]],[[0,0],[0]],[[36916,43],[43]],[[0,0],[0]],[[31908,2],[2]],[[0]],[[16627]],[[0]],[[5192]],[[0]],[[919]],[[0]],[[79]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
