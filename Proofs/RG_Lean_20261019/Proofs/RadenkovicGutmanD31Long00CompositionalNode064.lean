/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode062
import Proofs.RadenkovicGutmanD31Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0,0]],[[279,465],[465,2]],[[0,0],[0]],[[7737,1568],[1568]],[[0,0],[0]],[[40525,1722],[1722]],[[0,0],[0]],[[94022,726],[726]],[[0,0],[0]],[[119296,109],[109]],[[0,0],[0]],[[89840,2],[2]],[[0]],[[41239]],[[0]],[[11378]],[[0]],[[1763]],[[0]],[[127]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
