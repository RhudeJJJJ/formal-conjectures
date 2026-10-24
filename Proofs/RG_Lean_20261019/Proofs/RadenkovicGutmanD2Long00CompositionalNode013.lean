/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode008
import Proofs.RadenkovicGutmanD2Long00CompositionalNode012
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e013 : NestedArithmetic.Expr 3 := .times e008 e012
noncomputable def p013 : NestedHorner.Poly 3 := [[],[[3]],[[0]],[[13]],[[0]],[[16]],[[0]],[[7]],[[0]],[[1]]]
theorem step013 : p013=NestedArithmetic.mul p008 p012 := by decide +kernel
#print axioms step013
theorem h013 : NestedArithmetic.compile e013=p013 := StagedExprCompile.compile_times e013 e008 e012 p008 p012 p013 rfl h008 h012 step013
#print axioms h013
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
