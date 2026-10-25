/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode181
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e182 : NestedArithmetic.Expr 3 := .times e181 e122
noncomputable def p182 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step182 : p182=NestedArithmetic.mul p181 p122 := by decide +kernel
#print axioms step182
theorem h182 : NestedArithmetic.compile e182=p182 := StagedExprCompile.compile_times e182 e181 e122 p181 p122 p182 rfl h181 h122 step182
#print axioms h182
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
