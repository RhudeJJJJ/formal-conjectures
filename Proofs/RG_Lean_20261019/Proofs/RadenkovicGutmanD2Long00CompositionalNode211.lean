/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode174
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e211 : NestedArithmetic.Expr 3 := .times e017 e174
noncomputable def p211 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[34,0],[0,0]],[[0,0],[0,0]],[[244,0],[0,0]],[[0,0],[0,0]],[[962,0],[0,0]],[[0,0],[0,0]],[[2272,0],[0,0]],[[0,0],[0,0]],[[3288,2],[2,0]],[[0,0],[0,0]],[[2860,16],[16,0]],[[0,0],[0,0]],[[1394,44],[44,0]],[[0,0],[0,0]],[[318,48],[48,0]],[[0,0],[0,0]],[[18,18],[18,0]],[[0],[0,0]],[[0],[0,2]]]
theorem step211 : p211=NestedArithmetic.mul p017 p174 := by decide +kernel
#print axioms step211
theorem h211 : NestedArithmetic.compile e211=p211 := StagedExprCompile.compile_times e211 e017 e174 p017 p174 p211 rfl h017 h174 step211
#print axioms h211
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
