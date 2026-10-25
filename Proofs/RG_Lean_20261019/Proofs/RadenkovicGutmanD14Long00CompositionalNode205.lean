/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode204
import Proofs.RadenkovicGutmanD14Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[28,0],[0]],[[0,0],[0]],[[448,0],[0]],[[0,0],[0]],[[2996,0],[0]],[[0,0],[0]],[[10864,0],[0]],[[0,0],[0]],[[23184,0],[0]],[[0,0],[0]],[[29568,28],[28]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
