/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode017
import Proofs.RadenkovicGutmanD4Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e017 e000
noncomputable def p035 : NestedHorner.Poly 3 := [[[]],[[2]]]
theorem step035 : p035=NestedArithmetic.mul p017 p000 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e017 e000 p017 p000 p035 rfl h017 h000 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
