/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode035
import Proofs.RadenkovicGutmanD2Long00CompositionalNode036
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e056 : NestedArithmetic.Expr 3 := .times e035 e036
noncomputable def p056 : NestedHorner.Poly 3 := [[[]],[[0]]]
theorem step056 : p056=NestedArithmetic.mul p035 p036 := by decide +kernel
#print axioms step056
theorem h056 : NestedArithmetic.compile e056=p056 := StagedExprCompile.compile_times e056 e035 e036 p035 p036 p056 rfl h035 h036 step056
#print axioms h056
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
