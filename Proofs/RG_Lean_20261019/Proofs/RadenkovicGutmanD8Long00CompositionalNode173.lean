/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode165
import Proofs.RadenkovicGutmanD8Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-156,0],[0,0]],[[0,0],[0,0]],[[-776,0],[0,0]],[[0,0],[0,0]],[[-1676,0],[0,0]],[[0,0],[0,0]],[[-528,0],[0,0]],[[0,0],[0,0]],[[4656,-12],[-12,0]],[[0,0],[0,0]],[[9608,-88],[-88,0]],[[0,0],[0,0]],[[8468,-208],[-208,0]],[[0,0],[0,0]],[[3612,-160],[-160,0]],[[0,0],[0,0]],[[612,-4],[-4,0]],[[0,0],[0,0]],[[0,24],[24,-12]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
