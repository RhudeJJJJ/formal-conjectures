/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode005
import Proofs.RadenkovicGutmanD20Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e007 : NestedArithmetic.Expr 3 := .plus e005 e006
noncomputable def p007 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step007 : p007=NestedHorner.add p005 p006 := by decide +kernel
#print axioms step007
theorem h007 : NestedArithmetic.compile e007=p007 := StagedExprCompile.compile_plus e007 e005 e006 p005 p006 p007 rfl h005 h006 step007
#print axioms h007
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
