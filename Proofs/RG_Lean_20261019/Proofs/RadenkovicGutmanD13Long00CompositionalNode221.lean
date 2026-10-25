/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[338],[0],[0]],[[0,0],[0,0],[0]],[[10478,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[149058,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1289808,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7586748,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[32114732,507,0],[507,0],[0]],[[0,0,0],[0,0],[0]],[[101031242,11323,0],[11323,0],[0]],[[0,0,0],[0,0],[0]],[[240550882,112385,0],[112385,0],[0]],[[0,0,0],[0,0],[0]],[[437326032,653354,0],[653354,0],[0]],[[0,0,0],[0,0],[0]],[[608054902,2468921,0],[2468921,0],[0]],[[0,0,0],[0,0],[0]],[[643282614,6364371,169],[6364371,338],[169]],[[0,0,0],[0,0],[0]],[[511413604,11430484,2366],[11430484,4732],[2366]],[[0,0,0],[0,0],[0]],[[298892724,14354353,13689],[14354353,27378],[13689]],[[0,0,0],[0,0],[0]],[[123845904,12459187,42250],[12459187,84500],[42250]],[[0,0,0],[0,0],[0]],[[34213374,7258550,75036],[7258550,150072],[75036]],[[0,0,0],[0,0],[0]],[[5612490,2681523,77402],[2681523,154804],[77402]],[[0,0,0],[0,0],[0]],[[410670,561249,44785],[561249,89570],[44785]],[[0,0,0],[0,0],[0]],[[0,50193,13182],[50193,26364],[13182]],[[0,0,0],[0,0],[0]],[[0,0,1521],[0,3042],[1521]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
