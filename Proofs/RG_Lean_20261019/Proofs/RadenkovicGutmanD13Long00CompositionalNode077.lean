/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,1521],[0,3042],[1521]],[[0,0,0],[0,0],[0]],[[0,50193,13182],[50193,26364],[13182]],[[0,0,0],[0,0],[0]],[[410670,561249,44785],[561249,89570],[44785]],[[0,0,0],[0,0],[0]],[[5612490,2681523,77402],[2681523,154804],[77402]],[[0,0,0],[0,0],[0]],[[34213374,7258550,75036],[7258550,150072],[75036]],[[0,0,0],[0,0],[0]],[[123845904,12459187,42250],[12459187,84500],[42250]],[[0,0,0],[0,0],[0]],[[298892724,14354353,13689],[14354353,27378],[13689]],[[0,0,0],[0,0],[0]],[[511413604,11430484,2366],[11430484,4732],[2366]],[[0,0,0],[0,0],[0]],[[643282614,6364371,169],[6364371,338],[169]],[[0,0],[0]],[[608054902,2468921],[2468921]],[[0,0],[0]],[[437326032,653354],[653354]],[[0,0],[0]],[[240550882,112385],[112385]],[[0,0],[0]],[[101031242,11323],[11323]],[[0,0],[0]],[[32114732,507],[507]],[[0]],[[7586748]],[[0]],[[1289808]],[[0]],[[149058]],[[0]],[[10478]],[[0]],[[338]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
