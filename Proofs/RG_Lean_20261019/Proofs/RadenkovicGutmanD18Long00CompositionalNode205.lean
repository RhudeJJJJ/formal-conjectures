/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode204
import Proofs.RadenkovicGutmanD18Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[36,0],[0]],[[0,0],[0]],[[576,0],[0]],[[0,0],[0]],[[3852,0],[0]],[[0,0],[0]],[[13968,0],[0]],[[0,0],[0]],[[29808,0],[0]],[[0,0],[0]],[[38016,36],[36]],[[0,0],[0]],[[28044,252],[252]],[[0,0],[0]],[[10800,576],[576]],[[0,0],[0]],[[1620,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
