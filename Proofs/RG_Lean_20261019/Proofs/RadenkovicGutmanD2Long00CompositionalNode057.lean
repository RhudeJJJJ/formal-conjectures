/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode056
import Proofs.RadenkovicGutmanD2Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e056 e050
noncomputable def p057 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0,0],[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]]]
theorem step057 : p057=NestedArithmetic.mul p056 p050 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e056 e050 p056 p050 p057 rfl h056 h050 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
