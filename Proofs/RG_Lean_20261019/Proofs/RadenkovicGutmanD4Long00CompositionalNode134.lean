/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode002
import Proofs.RadenkovicGutmanD4Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e134 : NestedArithmetic.Expr 3 := .times e002 e001
noncomputable def p134 : NestedHorner.Poly 3 := [[[]],[[0]],[[0]],[[0]],[[3]]]
theorem step134 : p134=NestedArithmetic.mul p002 p001 := by decide +kernel
#print axioms step134
theorem h134 : NestedArithmetic.compile e134=p134 := StagedExprCompile.compile_times e134 e002 e001 p002 p001 p134 rfl h002 h001 step134
#print axioms h134
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
