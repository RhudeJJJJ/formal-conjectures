/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode013
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e014 : NestedArithmetic.Expr 3 := .times e013 e013
noncomputable def p014 : NestedHorner.Poly 3 := [[],[[]],[[9]],[[0]],[[78]],[[0]],[[265]],[[0]],[[458]],[[0]],[[444]],[[0]],[[250]],[[0]],[[81]],[[0]],[[14]],[[0]],[[1]]]
theorem step014 : p014=NestedArithmetic.mul p013 p013 := by decide +kernel
#print axioms step014
theorem h014 : NestedArithmetic.compile e014=p014 := StagedExprCompile.compile_times e014 e013 e013 p013 p013 p014 rfl h013 h013 step014
#print axioms h014
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
