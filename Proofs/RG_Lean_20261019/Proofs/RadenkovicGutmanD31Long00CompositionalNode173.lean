/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode165
import Proofs.RadenkovicGutmanD31Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-800,0],[0,0]],[[0,0],[0,0]],[[-4410,0],[0,0]],[[0,0],[0,0]],[[-12026,0],[0,0]],[[0,0],[0,0]],[[-15110,0],[0,0]],[[0,0],[0,0]],[[-864,-58],[-58,0]],[[0,0],[0,0]],[[20786,-433],[-433,0]],[[0,0],[0,0]],[[24798,-1059],[-1059,0]],[[0,0],[0,0]],[[12168,-896],[-896,0]],[[0,0],[0,0]],[[2268,-119],[-119,0]],[[0,0],[0,0]],[[0,93],[93,-58]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
