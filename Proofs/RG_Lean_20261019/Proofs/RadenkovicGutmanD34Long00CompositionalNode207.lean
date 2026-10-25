/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode065
import Proofs.RadenkovicGutmanD34Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-136,0],[0,0]],[[0,0],[0,0]],[[-1910,0],[0,0]],[[0,0],[0,0]],[[-12386,0],[0,0]],[[0,0],[0,0]],[[-45010,0],[0,0]],[[0,0],[0,0]],[[-98216,-2],[-2,0]],[[0,0],[0,0]],[[-130564,-118],[-118,0]],[[0,0],[0,0]],[[-102986,-792],[-792,0]],[[0,0],[0,0]],[[-44416,-1884],[-1884,0]],[[0,0],[0,0]],[[-8484,-1718],[-1718,0]],[[0,0],[0,0]],[[-306,-510],[-510,-2]],[[0],[0,0]],[[0],[0,-34]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
