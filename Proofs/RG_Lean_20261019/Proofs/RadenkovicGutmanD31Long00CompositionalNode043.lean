/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode041
import Proofs.RadenkovicGutmanD31Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,93],[93,-58]],[[0,0],[0]],[[2268,-119],[-119]],[[0,0],[0]],[[12168,-896],[-896]],[[0,0],[0]],[[24798,-1059],[-1059]],[[0,0],[0]],[[20786,-433],[-433]],[[0,0],[0]],[[-864,-58],[-58]],[[0]],[[-15110]],[[0]],[[-12026]],[[0]],[[-4410]],[[0]],[[-800]],[[0]],[[-58]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
