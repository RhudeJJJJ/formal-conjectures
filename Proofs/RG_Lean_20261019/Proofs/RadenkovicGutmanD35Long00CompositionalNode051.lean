/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode049
import Proofs.RadenkovicGutmanD35Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0,0]],[[-315,525],[525,2]],[[0,0],[0]],[[3903,1768],[1768]],[[0,0],[0]],[[32623,1938],[1938]],[[0,0],[0]],[[92464,814],[814]],[[0,0],[0]],[[135300,121],[121]],[[0,0],[0]],[[114588,2],[2]],[[0]],[[58097]],[[0]],[[17412]],[[0]],[[2869]],[[0]],[[209]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
