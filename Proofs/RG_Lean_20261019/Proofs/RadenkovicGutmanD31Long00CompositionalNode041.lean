/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode036
import Proofs.RadenkovicGutmanD31Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-58]],[[0,0],[0]],[[594,-522],[-522]],[[0,0],[0]],[[450,-1392],[-1392]],[[0,0],[0]],[[-7566,-1276],[-1276]],[[0,0],[0]],[[-26148,-464],[-464]],[[0,0],[0]],[[-40296,-58],[-58]],[[0]],[[-34888]],[[0]],[[-17854]],[[0]],[[-5340]],[[0]],[[-862]],[[0]],[[-58]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
