/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode034
import Proofs.RadenkovicGutmanD19Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-570,0],[0]],[[0,0],[0]],[[-3572,0],[0]],[[0,0],[0]],[[-12122,0],[0]],[[0,0],[0]],[[-24168,0],[0]],[[0,0],[0]],[[-28766,-19],[-19]],[[0,0],[0]],[[-19836,-133],[-133]],[[0,0],[0]],[[-7182,-304],[-304]],[[0,0],[0]],[[-1026,-247],[-247]],[[0,0],[0]],[[0,-57],[-57]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
