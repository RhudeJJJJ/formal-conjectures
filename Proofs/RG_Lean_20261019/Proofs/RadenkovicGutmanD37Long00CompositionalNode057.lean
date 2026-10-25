/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode034
import Proofs.RadenkovicGutmanD37Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-111],[-111]],[[0,0],[0]],[[-1665,-481],[-481]],[[0,0],[0]],[[-11100,-592],[-592]],[[0,0],[0]],[[-28823,-259],[-259]],[[0,0],[0]],[[-39072,-37],[-37]],[[0]],[[-30636]],[[0]],[[-14356]],[[0]],[[-3959]],[[0]],[[-592]],[[0]],[[-37]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
