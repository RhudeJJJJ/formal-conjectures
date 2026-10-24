/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .times e017 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0]],[[18,18],[18]],[[0,0],[0]],[[318,48],[48]],[[0,0],[0]],[[1394,44],[44]],[[0,0],[0]],[[2860,16],[16]],[[0,0],[0]],[[3288,2],[2]],[[0]],[[2272]],[[0]],[[962]],[[0]],[[244]],[[0]],[[34]],[[0]],[[2]]]
theorem step051 : p051=NestedArithmetic.mul p017 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_times e051 e017 e050 p017 p050 p051 rfl h017 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
