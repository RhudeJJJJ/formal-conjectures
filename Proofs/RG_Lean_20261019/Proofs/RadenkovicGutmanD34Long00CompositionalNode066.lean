/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode065
import Proofs.RadenkovicGutmanD34Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-34]],[[0,0],[0,0]],[[-306,-510],[-510,-2]],[[0,0],[0]],[[-8484,-1718],[-1718]],[[0,0],[0]],[[-44416,-1884],[-1884]],[[0,0],[0]],[[-102986,-792],[-792]],[[0,0],[0]],[[-130564,-118],[-118]],[[0,0],[0]],[[-98216,-2],[-2]],[[0]],[[-45010]],[[0]],[[-12386]],[[0]],[[-1910]],[[0]],[[-136]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
