/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode171
import Proofs.RadenkovicGutmanD31Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[62,0],[0]],[[0,0],[0]],[[930,0],[0]],[[0,0],[0]],[[5828,0],[0]],[[0,0],[0]],[[19778,0],[0]],[[0,0],[0]],[[39432,0],[0]],[[0,0],[0]],[[46934,31],[31]],[[0,0],[0]],[[32364,217],[217]],[[0,0],[0]],[[11718,496],[496]],[[0,0],[0]],[[1674,403],[403]],[[0,0],[0]],[[0,93],[93]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
