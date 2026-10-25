/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode059
import Proofs.RadenkovicGutmanD11Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,33],[33,-18]],[[0,0],[0]],[[333,-19],[-19]],[[0,0],[0]],[[438,-256],[-256]],[[0,0],[0]],[[-3977,-319],[-319]],[[0,0],[0]],[[-14124,-133],[-133]],[[0,0],[0]],[[-20484,-18],[-18]],[[0]],[[-16180]],[[0]],[[-7481]],[[0]],[[-2020]],[[0]],[[-295]],[[0]],[[-18]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
