/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode030
import Proofs.RadenkovicGutmanD43Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[86],[0]],[[0,0],[0]],[[1290,0],[0]],[[0,0],[0]],[[8084,0],[0]],[[0,0],[0]],[[27434,0],[0]],[[0,0],[0]],[[54696,0],[0]],[[0,0],[0]],[[65102,43],[43]],[[0,0],[0]],[[44892,301],[301]],[[0,0],[0]],[[16254,688],[688]],[[0,0],[0]],[[2322,559],[559]],[[0,0],[0]],[[0,129],[129]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
