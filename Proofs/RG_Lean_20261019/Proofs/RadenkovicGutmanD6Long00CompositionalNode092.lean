/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode089
import Proofs.RadenkovicGutmanD6Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,216],[0,216,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,0,2592],[0,8748,108],[2592,108]],[[0,0,0],[0,0,0],[0,0]],[[6804,71280,15660],[71280,48600,-996],[15660,-996]],[[0,0,0],[0,0,0],[0,0]],[[587412,656424,38196],[656424,105084,-1416],[38196,-1416]],[[0,0,0],[0,0,0],[0,0]],[[6648480,2653020,47088],[2653020,105912,-612],[47088,-612]],[[0,0,0],[0,0,0],[0,0]],[[35991900,6194280,29244],[6194280,37056,-84],[29244,-84]],[[0,0,0],[0,0],[0]],[[118908876,9257292,6072],[9257292,-20712],[6072]],[[0,0,0],[0,0],[0]],[[265923120,9261864,-2772],[9261864,-25668],[-2772]],[[0,0,0],[0,0],[0]],[[425312784,6283056,-1968],[6283056,-10392],[-1968]],[[0,0,0],[0,0],[0]],[[502143732,2838900,-444],[2838900,-1956],[-444]],[[0,0,0],[0,0],[0]],[[445563792,792432,-36],[792432,-144],[-36]],[[0,0],[0]],[[299580576,98940],[98940]],[[0,0],[0]],[[152572440,-12684],[-12684]],[[0,0],[0]],[[58267908,-7020],[-7020]],[[0,0],[0]],[[16284300,-1068],[-1068]],[[0,0],[0]],[[3158304,-60],[-60]],[[0]],[[370224]],[[0]],[[11820]],[[0]],[[-3420]],[[0]],[[-516]],[[0]],[[-24]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
