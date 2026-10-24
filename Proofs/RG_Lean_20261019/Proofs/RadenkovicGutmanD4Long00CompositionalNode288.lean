/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode287
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e288 : NestedArithmetic.Expr 3 := .times e287 e003
noncomputable def p288 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[64,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1920,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[26432,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[221312,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1259392,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5156224,64,0],[64,0],[0]],[[0,0,0],[0,0],[0]],[[15685312,1408,0],[1408,0],[0]],[[0,0,0],[0,0],[0]],[[36103808,13760,0],[13760,0],[0]],[[0,0,0],[0,0],[0]],[[63444608,78720,0],[78720,0],[0]],[[0,0,0],[0,0],[0]],[[85266048,292544,0],[292544,0],[0]],[[0,0,0],[0,0],[0]],[[87212224,741120,16],[741120,32],[16]],[[0,0,0],[0,0],[0]],[[67068288,1307264,224],[1307264,448],[224]],[[0,0,0],[0,0],[0]],[[37950336,1611520,1296],[1611520,2592],[1296]],[[0,0,0],[0,0],[0]],[[15244416,1372864,4000],[1372864,8000],[4000]],[[0,0,0],[0,0],[0]],[[4090176,785280,7104],[785280,14208],[7104]],[[0,0,0],[0,0],[0]],[[653184,285120,7328],[285120,14656],[7328]],[[0,0,0],[0,0],[0]],[[46656,58752,4240],[58752,8480],[4240]],[[0,0,0],[0,0],[0]],[[0,5184,1248],[5184,2496],[1248]],[[0,0,0],[0,0],[0]],[[0,0,144],[0,288],[144]]]
theorem step288 : p288=NestedArithmetic.mul p287 p003 := by decide +kernel
#print axioms step288
theorem h288 : NestedArithmetic.compile e288=p288 := StagedExprCompile.compile_times e288 e287 e003 p287 p003 p288 rfl h287 h003 step288
#print axioms h288
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
