/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode165
import Proofs.RadenkovicGutmanD44Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1164,0],[0,0]],[[0,0],[0,0]],[[-6464,0],[0,0]],[[0,0],[0,0]],[[-17876,0],[0,0]],[[0,0],[0,0]],[[-23352,0],[0,0]],[[0,0],[0,0]],[[-3984,-84],[-84,0]],[[0,0],[0,0]],[[27104,-628],[-628,0]],[[0,0],[0,0]],[[34028,-1540],[-1540,0]],[[0,0],[0,0]],[[17004,-1312],[-1312,0]],[[0,0],[0,0]],[[3204,-184],[-184,0]],[[0,0],[0,0]],[[0,132],[132,-84]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
