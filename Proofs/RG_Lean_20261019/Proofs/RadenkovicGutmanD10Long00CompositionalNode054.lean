/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode000
import Proofs.RadenkovicGutmanD10Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e054 : NestedArithmetic.Expr 3 := .times e000 e014
noncomputable def p054 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[9]],[[0]],[[78]],[[0]],[[265]],[[0]],[[458]],[[0]],[[444]],[[0]],[[250]],[[0]],[[81]],[[0]],[[14]],[[0]],[[1]]]
theorem step054 : p054=NestedArithmetic.mul p000 p014 := by decide +kernel
#print axioms step054
theorem h054 : NestedArithmetic.compile e054=p054 := StagedExprCompile.compile_times e054 e000 e014 p000 p014 p054 rfl h000 h014 step054
#print axioms h054
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
