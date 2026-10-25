/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode059
import Proofs.RadenkovicGutmanD42Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,126],[126,-80]],[[0,0],[0]],[[1170,-174],[-174]],[[0,0],[0]],[[-120,-1248],[-1248]],[[0,0],[0]],[[-23042,-1466],[-1466]],[[0,0],[0]],[[-70048,-598],[-598]],[[0,0],[0]],[[-96744,-80],[-80]],[[0]],[[-74584]],[[0]],[[-33986]],[[0]],[[-9088]],[[0]],[[-1318]],[[0]],[[-80]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
