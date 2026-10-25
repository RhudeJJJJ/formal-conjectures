/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[74],[0]],[[0,0],[0]],[[1110,0],[0]],[[0,0],[0]],[[6956,0],[0]],[[0,0],[0]],[[23606,0],[0]],[[0,0],[0]],[[47064,0],[0]],[[0,0],[0]],[[56018,37],[37]],[[0,0],[0]],[[38628,259],[259]],[[0,0],[0]],[[13986,592],[592]],[[0,0],[0]],[[1998,481],[481]],[[0,0],[0]],[[0,111],[111]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
