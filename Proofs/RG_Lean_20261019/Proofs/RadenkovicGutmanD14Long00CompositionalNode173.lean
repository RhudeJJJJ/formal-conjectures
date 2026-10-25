/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode165
import Proofs.RadenkovicGutmanD14Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-324,0],[0,0]],[[0,0],[0,0]],[[-1724,0],[0,0]],[[0,0],[0,0]],[[-4376,0],[0,0]],[[0,0],[0,0]],[[-4332,0],[0,0]],[[0,0],[0,0]],[[3216,-24],[-24,0]],[[0,0],[0,0]],[[12524,-178],[-178,0]],[[0,0],[0,0]],[[12728,-430],[-430,0]],[[0,0],[0,0]],[[5844,-352],[-352,0]],[[0,0],[0,0]],[[1044,-34],[-34,0]],[[0,0],[0,0]],[[0,42],[42,-24]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
