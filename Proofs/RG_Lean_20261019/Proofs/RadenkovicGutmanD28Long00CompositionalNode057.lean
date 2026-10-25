/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode034
import Proofs.RadenkovicGutmanD28Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-84],[-84]],[[0,0],[0]],[[-1260,-364],[-364]],[[0,0],[0]],[[-8400,-448],[-448]],[[0,0],[0]],[[-21812,-196],[-196]],[[0,0],[0]],[[-29568,-28],[-28]],[[0]],[[-23184]],[[0]],[[-10864]],[[0]],[[-2996]],[[0]],[[-448]],[[0]],[[-28]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
