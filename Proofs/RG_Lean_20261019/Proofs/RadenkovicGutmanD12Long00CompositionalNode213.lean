/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode030
import Proofs.RadenkovicGutmanD12Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[180,0],[0,0]],[[0,0],[0,0]],[[1128,0],[0,0]],[[0,0],[0,0]],[[3828,0],[0,0]],[[0,0],[0,0]],[[7632,0],[0,0]],[[0,0],[0,0]],[[9072,12],[12,0]],[[0,0],[0,0]],[[6168,96],[96,0]],[[0,0],[0,0]],[[2004,264],[264,0]],[[0,0],[0,0]],[[36,288],[288,0]],[[0,0],[0,0]],[[-108,108],[108,0]],[[0],[0,0]],[[0],[0,12]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
