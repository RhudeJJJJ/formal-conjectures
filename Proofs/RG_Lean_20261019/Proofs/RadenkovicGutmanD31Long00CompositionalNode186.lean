/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode178
import Proofs.RadenkovicGutmanD31Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-955,0],[0,0]],[[0,0],[0,0]],[[-6580,0],[0,0]],[[0,0],[0,0]],[[-24581,0],[0,0]],[[0,0],[0,0]],[[-53860,0],[0,0]],[[0,0],[0,0]],[[-69684,-58],[-58,0]],[[0,0],[0,0]],[[-50204,-433],[-433,0]],[[0,0],[0,0]],[[-16277,-1059],[-1059,0]],[[0,0],[0,0]],[[78,-896],[-896,0]],[[0,0],[0,0]],[[873,-119],[-119,0]],[[0,0],[0,0]],[[0,93],[93,-58]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
