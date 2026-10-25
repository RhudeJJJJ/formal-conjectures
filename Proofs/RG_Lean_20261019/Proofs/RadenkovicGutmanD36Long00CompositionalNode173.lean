/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode165
import Proofs.RadenkovicGutmanD36Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-940,0],[0,0]],[[0,0],[0,0]],[[-5200,0],[0,0]],[[0,0],[0,0]],[[-14276,0],[0,0]],[[0,0],[0,0]],[[-18280,0],[0,0]],[[0,0],[0,0]],[[-2064,-68],[-68,0]],[[0,0],[0,0]],[[23216,-508],[-508,0]],[[0,0],[0,0]],[[28348,-1244],[-1244,0]],[[0,0],[0,0]],[[14028,-1056],[-1056,0]],[[0,0],[0,0]],[[2628,-144],[-144,0]],[[0,0],[0,0]],[[0,108],[108,-68]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
