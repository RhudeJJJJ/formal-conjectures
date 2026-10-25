/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e030 e056
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,84],[84]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[29568,28],[28]],[[0]],[[23184]],[[0]],[[10864]],[[0]],[[2996]],[[0]],[[448]],[[0]],[[28]]]
theorem step060 : p060=NestedArithmetic.mul p030 p056 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e030 e056 p030 p056 p060 rfl h030 h056 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
