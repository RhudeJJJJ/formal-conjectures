/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode204
import Proofs.RadenkovicGutmanD31Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[62,0],[0]],[[0,0],[0]],[[992,0],[0]],[[0,0],[0]],[[6634,0],[0]],[[0,0],[0]],[[24056,0],[0]],[[0,0],[0]],[[51336,0],[0]],[[0,0],[0]],[[65472,62],[62]],[[0,0],[0]],[[48298,434],[434]],[[0,0],[0]],[[18600,992],[992]],[[0,0],[0]],[[2790,806],[806]],[[0,0],[0]],[[0,186],[186]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
