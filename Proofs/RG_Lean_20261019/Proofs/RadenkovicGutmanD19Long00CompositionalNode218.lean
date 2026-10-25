/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode034
import Proofs.RadenkovicGutmanD19Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-19],[0]],[[0,0],[0]],[[-304,0],[0]],[[0,0],[0]],[[-2033,0],[0]],[[0,0],[0]],[[-7372,0],[0]],[[0,0],[0]],[[-15732,0],[0]],[[0,0],[0]],[[-20064,-19],[-19]],[[0,0],[0]],[[-14801,-133],[-133]],[[0,0],[0]],[[-5700,-304],[-304]],[[0,0],[0]],[[-855,-247],[-247]],[[0,0],[0]],[[0,-57],[-57]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
