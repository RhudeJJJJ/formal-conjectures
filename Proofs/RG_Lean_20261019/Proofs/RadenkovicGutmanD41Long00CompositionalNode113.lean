/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-30258,30258],[0,30258]],[[0,0,0],[0,0,0],[0,0]],[[136161,-272322,136161],[-272322,282408,80688],[136161,80688]],[[0,0,0],[0,0,0],[0,0]],[[-90774,-635418,726192],[-635418,2013838,73964],[726192,73964]],[[0,0,0],[0,0,0],[0,0]],[[-5037957,4629474,1633932],[4629474,4995932,26896],[1633932,26896]],[[0,0,0],[0,0,0],[0,0]],[[-13868250,29007336,2017200],[29007336,6576072,3362],[2017200,3362]],[[0,0,0],[0,0],[0]],[[29190565,76751098,1489366],[76751098,5116964],[1489366]],[[0,0,0],[0,0],[0]],[[276968284,122763430,672400],[122763430,2417278],[672400]],[[0,0,0],[0,0],[0]],[[865335094,131272652,181548],[131272652,679124],[181548]],[[0,0,0],[0,0],[0]],[[1663877334,97686272,26896],[97686272,104222],[26896]],[[0,0,0],[0,0],[0]],[[2239401304,51280586,1681],[51280586,6724],[1681]],[[0,0],[0]],[[2220654792,18911250],[18911250]],[[0,0],[0]],[[1661621432,4790850],[4790850]],[[0,0],[0]],[[947495650,793432],[793432]],[[0,0],[0]],[[411907197,77326],[77326]],[[0,0],[0]],[[135428084,3362],[3362]],[[0]],[[33078718]],[[0]],[[5812898]],[[0]],[[694253]],[[0]],[[50430]],[[0]],[[1681]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
