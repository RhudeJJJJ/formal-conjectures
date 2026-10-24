/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode034
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e034 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,144],[0,288],[144]],[[0,0,0],[0,0],[0]],[[0,5184,1248],[5184,2496],[1248]],[[0,0,0],[0,0],[0]],[[46656,58752,4240],[58752,8480],[4240]],[[0,0,0],[0,0],[0]],[[653184,285120,7328],[285120,14656],[7328]],[[0,0,0],[0,0],[0]],[[4090176,785280,7104],[785280,14208],[7104]],[[0,0,0],[0,0],[0]],[[15244416,1372864,4000],[1372864,8000],[4000]],[[0,0,0],[0,0],[0]],[[37950336,1611520,1296],[1611520,2592],[1296]],[[0,0,0],[0,0],[0]],[[67068288,1307264,224],[1307264,448],[224]],[[0,0,0],[0,0],[0]],[[87212224,741120,16],[741120,32],[16]],[[0,0],[0]],[[85266048,292544],[292544]],[[0,0],[0]],[[63444608,78720],[78720]],[[0,0],[0]],[[36103808,13760],[13760]],[[0,0],[0]],[[15685312,1408],[1408]],[[0,0],[0]],[[5156224,64],[64]],[[0]],[[1259392]],[[0]],[[221312]],[[0]],[[26432]],[[0]],[[1920]],[[0]],[[64]]]
theorem step113 : p113=NestedArithmetic.power p034 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e034 p034 p113 rfl h034 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
