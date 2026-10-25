/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode059
import Proofs.RadenkovicGutmanD44Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,132],[132,-84]],[[0,0],[0]],[[1224,-184],[-184]],[[0,0],[0]],[[-156,-1312],[-1312]],[[0,0],[0]],[[-24272,-1540],[-1540]],[[0,0],[0]],[[-73656,-628],[-628]],[[0,0],[0]],[[-101664,-84],[-84]],[[0]],[[-78352]],[[0]],[[-35696]],[[0]],[[-9544]],[[0]],[[-1384]],[[0]],[[-84]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
