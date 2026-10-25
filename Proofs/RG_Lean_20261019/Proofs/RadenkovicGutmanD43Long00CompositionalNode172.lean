/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode171
import Proofs.RadenkovicGutmanD43Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[86,0],[0]],[[0,0],[0]],[[1290,0],[0]],[[0,0],[0]],[[8084,0],[0]],[[0,0],[0]],[[27434,0],[0]],[[0,0],[0]],[[54696,0],[0]],[[0,0],[0]],[[65102,43],[43]],[[0,0],[0]],[[44892,301],[301]],[[0,0],[0]],[[16254,688],[688]],[[0,0],[0]],[[2322,559],[559]],[[0,0],[0]],[[0,129],[129]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
