/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode092
import Proofs.RadenkovicGutmanD44Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3168,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28512,-28512,0],[-28512,-26664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-743688,-316008,0],[-316008,-86416,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7225416,-1487376,0],[-1487376,-137896,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38096256,-3927000,0],[-3927000,-115984,0],[0,0]],[[0,0,0],[0,0],[0]],[[-126538984,-6470992,0],[-6470992,-48928],[0]],[[0,0,0],[0,0],[0]],[[-286004664,-6975672,0],[-6975672,-6512],[0]],[[0,0,0],[0,0],[0]],[[-459752304,-4974112,0],[-4974112,2200],[0]],[[0,0,0],[0,0],[0]],[[-539057024,-2278672,0],[-2278672,880],[0]],[[0,0,0],[0,0],[0]],[[-466348696,-589952,0],[-589952,88],[0]],[[0,0],[0]],[[-297160688,-30712],[-30712]],[[0,0],[0]],[[-136621936,32560],[32560]],[[0,0],[0]],[[-42576160,11176],[11176]],[[0,0],[0]],[[-7139352,1584],[1584]],[[0,0],[0]],[[460328,88],[88]],[[0]],[[632016]],[[0]],[[180576]],[[0]],[[27896]],[[0]],[[2376]],[[0]],[[88]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
