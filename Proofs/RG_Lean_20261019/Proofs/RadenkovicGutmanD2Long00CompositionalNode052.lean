/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode000
import Proofs.RadenkovicGutmanD2Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e052 : NestedArithmetic.Expr 3 := .times e000 e014
noncomputable def p052 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[9]],[[0]],[[78]],[[0]],[[265]],[[0]],[[458]],[[0]],[[444]],[[0]],[[250]],[[0]],[[81]],[[0]],[[14]],[[0]],[[1]]]
theorem step052 : p052=NestedArithmetic.mul p000 p014 := by decide +kernel
#print axioms step052
theorem h052 : NestedArithmetic.compile e052=p052 := StagedExprCompile.compile_times e052 e000 e014 p000 p014 p052 rfl h000 h014 step052
#print axioms h052
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
