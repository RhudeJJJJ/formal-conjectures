/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1536],[0,-1536,448]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-18432],[0,-63360,1312],[-18432,1312]],[[0,0,0],[0,0,0],[0,0]],[[-67392,-515808,-101280],[-515808,-314976,12896],[-101280,12896]],[[0,0,0],[0,0,0],[0,0]],[[-4571424,-4569696,-215456],[-4569696,-554048,15616],[-215456,15616]],[[0,0,0],[0,0,0],[0,0]],[[-49724064,-17682624,-203328],[-17682624,-277216,6432],[-203328,6432]],[[0,0,0],[0,0,0],[0,0]],[[-261905664,-39118560,-39584],[-39118560,367808,864],[-39584,864]],[[0,0,0],[0,0],[0]],[[-843100192,-54297600,85248],[-54297600,643200],[85248]],[[0,0,0],[0,0],[0]],[[-1832633696,-48488992,79392],[-48488992,418880],[79392]],[[0,0,0],[0,0],[0]],[[-2833330880,-26785984,30528],[-26785984,140832],[30528]],[[0,0,0],[0,0],[0]],[[-3204235008,-7233888,5664],[-7233888,24256],[5664]],[[0,0,0],[0,0],[0]],[[-2683867616,1016160,416],[1016160,1696],[416]],[[0,0],[0]],[[-1662371968,1703872],[1703872]],[[0,0],[0]],[[-745929984,690304],[690304]],[[0,0],[0]],[[-227963008,147904],[147904]],[[0,0],[0]],[[-37908448,17024],[17024]],[[0,0],[0]],[[2110368,832],[832]],[[0]],[[3117760]],[[0]],[[883584]],[[0]],[[134944]],[[0]],[[11360]],[[0]],[[416]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
