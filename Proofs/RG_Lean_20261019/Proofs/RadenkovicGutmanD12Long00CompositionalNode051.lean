/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode049
import Proofs.RadenkovicGutmanD12Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0,0]],[[-108,180],[180,2]],[[0,0],[0]],[[1350,618],[618]],[[0,0],[0]],[[11394,696],[696]],[[0,0],[0]],[[32618,308],[308]],[[0,0],[0]],[[48268,52],[52]],[[0,0],[0]],[[41448,2],[2]],[[0]],[[21412]],[[0]],[[6602]],[[0]],[[1144]],[[0]],[[94]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
