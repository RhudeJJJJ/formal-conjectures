/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode034
import Proofs.RadenkovicGutmanD38Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-114],[-114]],[[0,0],[0]],[[-1710,-494],[-494]],[[0,0],[0]],[[-11400,-608],[-608]],[[0,0],[0]],[[-29602,-266],[-266]],[[0,0],[0]],[[-40128,-38],[-38]],[[0]],[[-31464]],[[0]],[[-14744]],[[0]],[[-4066]],[[0]],[[-608]],[[0]],[[-38]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
