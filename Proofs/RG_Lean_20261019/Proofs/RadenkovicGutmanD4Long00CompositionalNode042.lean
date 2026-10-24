/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode040
import Proofs.RadenkovicGutmanD4Long00CompositionalNode041
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .plus e040 e041
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,12],[12,-4]],[[0,0],[0]],[[324,16],[16]],[[0,0],[0]],[[2124,-32],[-32]],[[0,0],[0]],[[5628,-60],[-60]],[[0,0],[0]],[[7664,-28],[-28]],[[0,0],[0]],[[5616,-4],[-4]],[[0]],[[2008]],[[0]],[[124]],[[0]],[[-144]],[[0]],[[-44]],[[0]],[[-4]]]
theorem step042 : p042=NestedHorner.add p040 p041 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_plus e042 e040 e041 p040 p041 p042 rfl h040 h041 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
