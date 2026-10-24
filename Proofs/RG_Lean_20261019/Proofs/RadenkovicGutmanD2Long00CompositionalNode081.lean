/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode068
import Proofs.RadenkovicGutmanD2Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e068 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,48],[0,48,8]],[[0,0,0],[0,0,0],[0,0,0]],[[0,432,576],[432,2016,400],[576,400,4]],[[0,0,0],[0,0,0],[0,0]],[[7128,22464,5352],[22464,18912,920],[5352,920]],[[0,0,0],[0,0,0],[0,0]],[[226908,226080,19396],[226080,69104,912],[19396,912]],[[0,0,0],[0,0,0],[0,0]],[[2397384,1066840,37296],[1066840,134528,432],[37296,432]],[[0,0,0],[0,0,0],[0,0]],[[13424268,2969664,42880],[2969664,157312,96],[42880,96]],[[0,0,0],[0,0,0],[0,0]],[[47433496,5411296,31168],[5411296,116672,8],[31168,8]],[[0,0,0],[0,0],[0]],[[115586492,6829280,14648],[6829280,56000],[14648]],[[0,0,0],[0,0],[0]],[[204651664,6165800,4432],[6165800,17280],[4432]],[[0,0,0],[0,0],[0]],[[272087608,4053520,832],[4053520,3296],[832]],[[0,0,0],[0,0],[0]],[[277495440,1953872,88],[1953872,352],[88]],[[0,0,0],[0,0],[0]],[[220060720,688512,4],[688512,16],[4]],[[0,0],[0]],[[136748816,174904],[174904]],[[0,0],[0]],[[66776928,31104],[31104]],[[0,0],[0]],[[25576888,3664],[3664]],[[0,0],[0]],[[7630844,256],[256]],[[0,0],[0]],[[1750064,8],[8]],[[0]],[[301816]],[[0]],[[37768]],[[0]],[[3228]],[[0]],[[168]],[[0]],[[4]]]
theorem step081 : p081=NestedHorner.add p068 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e068 e080 p068 p080 p081 rfl h068 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
