/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode112
import Proofs.RadenkovicGutmanD7Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,168],[0,168,128]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1512,3276],[1512,6336,3200],[3276,3200,4]],[[0,0,0],[0,0,0],[0,0]],[[51192,96336,37752],[96336,92424,7840],[37752,7840]],[[0,0,0],[0,0,0],[0,0]],[[1423548,1140984,147376],[1140984,390848,7112],[147376,7112]],[[0,0,0],[0,0,0],[0,0]],[[15062328,5893472,287536],[5893472,807848,2672],[287536,2672]],[[0,0,0],[0,0,0],[0,0]],[[86020404,17289704,322520],[17289704,959856,376],[322520,376]],[[0,0,0],[0,0,0],[0,0]],[[309578000,32442472,220688],[32442472,698304,8],[220688,8]],[[0,0,0],[0,0],[0]],[[764059060,41447336,93748],[41447336,316080],[93748]],[[0,0,0],[0,0],[0]],[[1361071728,37315248,24272],[37315248,87208],[24272]],[[0,0,0],[0,0],[0]],[[1807989216,24089504,3572],[24089504,13648],[3572]],[[0,0,0],[0,0],[0]],[[1829082936,11203272,248],[11203272,1000],[248]],[[0,0,0],[0,0],[0]],[[1427919088,3725904,4],[3725904,16],[4]],[[0,0],[0]],[[866273616,866824],[866824]],[[0,0],[0]],[[409083896,134960],[134960]],[[0,0],[0]],[[149821248,12896],[12896]],[[0,0],[0]],[[42136916,624],[624]],[[0,0],[0]],[[8939344,8],[8]],[[0]],[[1388496]],[[0]],[[150208]],[[0]],[[10348]],[[0]],[[376]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
