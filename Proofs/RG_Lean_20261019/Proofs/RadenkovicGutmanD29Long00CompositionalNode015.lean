/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanD29Long00CompositionalNode007
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e015 : NestedArithmetic.Expr 3 := .times e003 e007
noncomputable def p015 : NestedHorner.Poly 3 := [[],[[]],[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step015 : p015=NestedArithmetic.mul p003 p007 := by decide +kernel
#print axioms step015
theorem h015 : NestedArithmetic.compile e015=p015 := StagedExprCompile.compile_times e015 e003 e007 p003 p007 p015 rfl h003 h007 step015
#print axioms h015
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
