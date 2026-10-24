/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode065
import Proofs.RadenkovicGutmanD2Long00CompositionalNode067
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e068 : NestedArithmetic.Expr 3 := .plus e065 e067
noncomputable def p068 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,36],[0,72,120],[36,120,8]],[[0,0,0],[0,0,0],[0,0,0]],[[-324,1620,1212],[1620,3936,592],[1212,592,4]],[[0,0,0],[0,0,0],[0,0]],[[11232,41580,8140],[41580,27944,1096],[8140,1096]],[[0,0,0],[0,0,0],[0,0]],[[342576,336204,25116],[336204,88320,976],[25116,976]],[[0,0,0],[0,0,0],[0,0]],[[3288768,1405824,43872],[1405824,157280,440],[43872,440]],[[0,0,0],[0,0,0],[0,0]],[[17133224,3618796,47424],[3618796,173488,96],[47424,96]],[[0,0,0],[0,0,0],[0,0]],[[57378696,6244604,33092],[6244604,123720,8],[33092,8]],[[0,0,0],[0,0],[0]],[[134249252,7575600,15136],[7575600,57840],[15136]],[[0,0,0],[0,0],[0]],[[230321336,6641524,4500],[6641524,17544],[4500]],[[0,0,0],[0,0],[0]],[[298696288,4270548,836],[4270548,3312],[836]],[[0,0,0],[0,0],[0]],[[298630880,2024176,88],[2024176,352],[88]],[[0,0,0],[0,0],[0]],[[233038840,704292,4],[704292,16],[4]],[[0,0],[0]],[[142924568,177236],[177236]],[[0,0],[0]],[[69046124,31308],[31308]],[[0,0],[0]],[[26213992,3672],[3672]],[[0,0],[0]],[[7764884,256],[256]],[[0,0],[0]],[[1770504,8],[8]],[[0]],[[303948]],[[0]],[[37904]],[[0]],[[3232]],[[0]],[[168]],[[0]],[[4]]]
theorem step068 : p068=NestedHorner.add p065 p067 := by decide +kernel
#print axioms step068
theorem h068 : NestedArithmetic.compile e068=p068 := StagedExprCompile.compile_plus e068 e065 e067 p065 p067 p068 rfl h065 h067 step068
#print axioms h068
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
