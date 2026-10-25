/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode171
import Proofs.RadenkovicGutmanD36Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[72,0],[0]],[[0,0],[0]],[[1080,0],[0]],[[0,0],[0]],[[6768,0],[0]],[[0,0],[0]],[[22968,0],[0]],[[0,0],[0]],[[45792,0],[0]],[[0,0],[0]],[[54504,36],[36]],[[0,0],[0]],[[37584,252],[252]],[[0,0],[0]],[[13608,576],[576]],[[0,0],[0]],[[1944,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
