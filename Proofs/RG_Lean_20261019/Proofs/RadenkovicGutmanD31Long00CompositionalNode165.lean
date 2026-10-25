/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode164
import Proofs.RadenkovicGutmanD31Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-862,0],[0,0]],[[0,0],[0,0]],[[-5340,0],[0,0]],[[0,0],[0,0]],[[-17854,0],[0,0]],[[0,0],[0,0]],[[-34888,0],[0,0]],[[0,0],[0,0]],[[-40296,-58],[-58,0]],[[0,0],[0,0]],[[-26148,-464],[-464,0]],[[0,0],[0,0]],[[-7566,-1276],[-1276,0]],[[0,0],[0,0]],[[450,-1392],[-1392,0]],[[0,0],[0,0]],[[594,-522],[-522,0]],[[0],[0,0]],[[0],[0,-58]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
