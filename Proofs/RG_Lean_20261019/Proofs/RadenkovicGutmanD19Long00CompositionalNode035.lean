/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode034
import Proofs.RadenkovicGutmanD19Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e035 : NestedArithmetic.Expr 3 := .times e034 e028
noncomputable def p035 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-57],[-57]],[[0,0],[0]],[[-1026,-247],[-247]],[[0,0],[0]],[[-7182,-304],[-304]],[[0,0],[0]],[[-19836,-133],[-133]],[[0,0],[0]],[[-28766,-19],[-19]],[[0]],[[-24168]],[[0]],[[-12122]],[[0]],[[-3572]],[[0]],[[-570]],[[0]],[[-38]]]
theorem step035 : p035=NestedArithmetic.mul p034 p028 := by decide +kernel
#print axioms step035
theorem h035 : NestedArithmetic.compile e035=p035 := StagedExprCompile.compile_times e035 e034 e028 p034 p028 p035 rfl h034 h028 step035
#print axioms h035
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
