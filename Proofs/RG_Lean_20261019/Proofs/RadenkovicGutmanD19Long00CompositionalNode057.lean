/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode034
import Proofs.RadenkovicGutmanD19Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-57],[-57]],[[0,0],[0]],[[-855,-247],[-247]],[[0,0],[0]],[[-5700,-304],[-304]],[[0,0],[0]],[[-14801,-133],[-133]],[[0,0],[0]],[[-20064,-19],[-19]],[[0]],[[-15732]],[[0]],[[-7372]],[[0]],[[-2033]],[[0]],[[-304]],[[0]],[[-19]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
