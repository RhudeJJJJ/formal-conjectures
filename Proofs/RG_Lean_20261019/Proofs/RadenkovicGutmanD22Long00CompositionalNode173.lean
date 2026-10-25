/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode165
import Proofs.RadenkovicGutmanD22Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-548,0],[0,0]],[[0,0],[0,0]],[[-2988,0],[0,0]],[[0,0],[0,0]],[[-7976,0],[0,0]],[[0,0],[0,0]],[[-9404,0],[0,0]],[[0,0],[0,0]],[[1296,-40],[-40,0]],[[0,0],[0,0]],[[16412,-298],[-298,0]],[[0,0],[0,0]],[[18408,-726],[-726,0]],[[0,0],[0,0]],[[8820,-608],[-608,0]],[[0,0],[0,0]],[[1620,-74],[-74,0]],[[0,0],[0,0]],[[0,66],[66,-40]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
