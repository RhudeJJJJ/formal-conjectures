/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode034
import Proofs.RadenkovicGutmanD33Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-99],[-99]],[[0,0],[0]],[[-1485,-429],[-429]],[[0,0],[0]],[[-9900,-528],[-528]],[[0,0],[0]],[[-25707,-231],[-231]],[[0,0],[0]],[[-34848,-33],[-33]],[[0]],[[-27324]],[[0]],[[-12804]],[[0]],[[-3531]],[[0]],[[-528]],[[0]],[[-33]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
