/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode030
import Proofs.RadenkovicGutmanD33Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[66],[0]],[[0,0],[0]],[[990,0],[0]],[[0,0],[0]],[[6204,0],[0]],[[0,0],[0]],[[21054,0],[0]],[[0,0],[0]],[[41976,0],[0]],[[0,0],[0]],[[49962,33],[33]],[[0,0],[0]],[[34452,231],[231]],[[0,0],[0]],[[12474,528],[528]],[[0,0],[0]],[[1782,429],[429]],[[0,0],[0]],[[0,99],[99]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
