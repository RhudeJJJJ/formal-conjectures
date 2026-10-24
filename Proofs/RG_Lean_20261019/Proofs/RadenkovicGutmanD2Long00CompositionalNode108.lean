/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e108 : NestedArithmetic.Expr 3 := .pow e042 2
noncomputable def p108 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,36],[0,72,0],[36,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,2160,312],[2160,624,0],[312,0]],[[0,0,0],[0,0,0],[0,0]],[[32400,25920,1060],[25920,2120,0],[1060,0]],[[0,0,0],[0,0,0],[0,0]],[[496800,133776,1832],[133776,3664,0],[1832,0]],[[0,0,0],[0,0,0],[0,0]],[[3419280,392480,1776],[392480,3552,0],[1776,0]],[[0,0,0],[0,0,0],[0,0]],[[14023200,729808,1000],[729808,2000,0],[1000,0]],[[0,0,0],[0,0],[0]],[[38371744,907936,324],[907936,648],[324]],[[0,0,0],[0,0],[0]],[[74324192,776992,56],[776992,112],[56]],[[0,0,0],[0,0],[0]],[[105497200,462432,4],[462432,8],[4]],[[0,0,0],[0,0],[0]],[[112047840,190736,0],[190736,0],[0]],[[0,0,0],[0,0],[0]],[[90104224,53408,0],[53408,0],[0]],[[0,0],[0]],[[55126880,9680],[9680]],[[0,0],[0]],[[25619824,1024],[1024]],[[0,0],[0]],[[8966880,48],[48]],[[0,0],[0]],[[2321824,0],[0]],[[0,0],[0]],[[430880,0],[0]],[[0]],[[54160]],[[0]],[[4128]],[[0]],[[144]],[[0]],[[0]],[[0]],[[0]]]
theorem step108 : p108=NestedArithmetic.power p042 2 := by decide +kernel
#print axioms step108
theorem h108 : NestedArithmetic.compile e108=p108 := StagedExprCompile.compile_pow 2 e108 e042 p042 p108 rfl h042 step108
#print axioms h108
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
