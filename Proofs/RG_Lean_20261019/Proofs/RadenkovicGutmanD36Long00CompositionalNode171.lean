/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode030
import Proofs.RadenkovicGutmanD36Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[72],[0]],[[0,0],[0]],[[1080,0],[0]],[[0,0],[0]],[[6768,0],[0]],[[0,0],[0]],[[22968,0],[0]],[[0,0],[0]],[[45792,0],[0]],[[0,0],[0]],[[54504,36],[36]],[[0,0],[0]],[[37584,252],[252]],[[0,0],[0]],[[13608,576],[576]],[[0,0],[0]],[[1944,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
