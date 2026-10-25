/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode171
import Proofs.RadenkovicGutmanD14Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[28,0],[0]],[[0,0],[0]],[[420,0],[0]],[[0,0],[0]],[[2632,0],[0]],[[0,0],[0]],[[8932,0],[0]],[[0,0],[0]],[[17808,0],[0]],[[0,0],[0]],[[21196,14],[14]],[[0,0],[0]],[[14616,98],[98]],[[0,0],[0]],[[5292,224],[224]],[[0,0],[0]],[[756,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
