/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode119
import Proofs.RadenkovicGutmanD31Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-862,0],[0,0]],[[0,0],[0,0]],[[-5340,0],[0,0]],[[0,0],[0,0]],[[-17854,0],[0,0]],[[0,0],[0,0]],[[-34888,0],[0,0]],[[0,0],[0,0]],[[-40296,-58],[-58,0]],[[0,0],[0,0]],[[-26148,-464],[-464,0]],[[0,0],[0,0]],[[-7566,-1276],[-1276,0]],[[0,0],[0,0]],[[450,-1392],[-1392,0]],[[0,0],[0,0]],[[594,-522],[-522,0]],[[0],[0,0]],[[0],[0,-58]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
