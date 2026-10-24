/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode058
import Proofs.RadenkovicGutmanD4Long00CompositionalNode059
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .plus e058 e059
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,12],[12,-4]],[[0,0],[0]],[[144,16],[16]],[[0,0],[0]],[[564,-32],[-32]],[[0,0],[0]],[[328,-60],[-60]],[[0,0],[0]],[[-1496,-28],[-28]],[[0,0],[0]],[[-3264,-4],[-4]],[[0]],[[-2992]],[[0]],[[-1496]],[[0]],[[-424]],[[0]],[[-64]],[[0]],[[-4]]]
theorem step060 : p060=NestedHorner.add p058 p059 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_plus e060 e058 e059 p058 p059 p060 rfl h058 h059 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
