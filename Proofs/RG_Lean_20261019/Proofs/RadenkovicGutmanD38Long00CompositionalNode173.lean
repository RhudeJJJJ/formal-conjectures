/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode165
import Proofs.RadenkovicGutmanD38Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-996,0],[0,0]],[[0,0],[0,0]],[[-5516,0],[0,0]],[[0,0],[0,0]],[[-15176,0],[0,0]],[[0,0],[0,0]],[[-19548,0],[0,0]],[[0,0],[0,0]],[[-2544,-72],[-72,0]],[[0,0],[0,0]],[[24188,-538],[-538,0]],[[0,0],[0,0]],[[29768,-1318],[-1318,0]],[[0,0],[0,0]],[[14772,-1120],[-1120,0]],[[0,0],[0,0]],[[2772,-154],[-154,0]],[[0,0],[0,0]],[[0,114],[114,-72]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
