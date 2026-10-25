/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode171
import Proofs.RadenkovicGutmanD33Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[66,0],[0]],[[0,0],[0]],[[990,0],[0]],[[0,0],[0]],[[6204,0],[0]],[[0,0],[0]],[[21054,0],[0]],[[0,0],[0]],[[41976,0],[0]],[[0,0],[0]],[[49962,33],[33]],[[0,0],[0]],[[34452,231],[231]],[[0,0],[0]],[[12474,528],[528]],[[0,0],[0]],[[1782,429],[429]],[[0,0],[0]],[[0,99],[99]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
