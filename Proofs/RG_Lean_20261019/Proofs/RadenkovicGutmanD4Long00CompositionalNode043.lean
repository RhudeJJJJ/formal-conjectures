/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode018
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e018 e009
noncomputable def p043 : NestedHorner.Poly 3 := [[[4]],[[0]],[[2]]]
theorem step043 : p043=NestedHorner.add p018 p009 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e018 e009 p018 p009 p043 rfl h018 h009 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
