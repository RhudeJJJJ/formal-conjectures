/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode075
import Proofs.RadenkovicGutmanD27Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0]],[[0,0,6561],[0,13122,13122],[6561,13122]],[[0,0,0],[0,0,0],[0,0]],[[-59049,216513,115911],[216513,349920,34992],[115911,34992]],[[0,0,0],[0,0,0],[0,0]],[[747954,3483891,508113],[3483891,1646082,32076],[508113,32076]],[[0,0,0],[0,0,0],[0,0]],[[21080493,20070099,1042470],[20070099,3502116,11664],[1042470,11664]],[[0,0,0],[0,0,0],[0,0]],[[162454734,61779834,1198476],[61779834,4146552,1458],[1198476,1458]],[[0,0,0],[0,0],[0]],[[675957231,118304307,828144],[118304307,2948076],[828144]],[[0,0,0],[0,0],[0]],[[1812512700,151870383,350649],[151870383,1284498],[350649]],[[0,0,0],[0,0],[0]],[[3401288010,136016820,88938],[136016820,335340],[88938]],[[0,0,0],[0,0],[0]],[[4678297722,86700699,12393],[86700699,48114],[12393]],[[0,0,0],[0,0],[0]],[[4849431930,39553353,729],[39553353,2916],[729]],[[0,0],[0]],[[3851933940,12812904],[12812904]],[[0,0],[0]],[[2365262370,2875905],[2875905]],[[0,0],[0]],[[1125530802,425007],[425007]],[[0,0],[0]],[[413560971,37179],[37179]],[[0,0],[0]],[[116112204,1458],[1458]],[[0]],[[24428790]],[[0]],[[3725190]],[[0]],[[388557]],[[0]],[[24786]],[[0]],[[729]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
