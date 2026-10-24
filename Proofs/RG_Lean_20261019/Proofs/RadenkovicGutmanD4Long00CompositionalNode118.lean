/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode017
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e118 : NestedArithmetic.Expr 3 := .times e017 e006
noncomputable def p118 : NestedHorner.Poly 3 := [[[2]]]
theorem step118 : p118=NestedArithmetic.mul p017 p006 := by decide +kernel
#print axioms step118
theorem h118 : NestedArithmetic.compile e118=p118 := StagedExprCompile.compile_times e118 e017 e006 p017 p006 p118 rfl h017 h006 step118
#print axioms h118
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
