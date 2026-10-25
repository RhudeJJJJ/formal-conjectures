/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode033
import Proofs.RadenkovicGutmanD40Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1600]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,28800],[0,28800]],[[0,0,0],[0,0,0],[0,0]],[[-129600,0,129600],[0,518400,76800],[129600,76800]],[[0,0,0],[0,0,0],[0,0]],[[-2246400,2332800,691200],[2332800,2764800,70400],[691200,70400]],[[0,0,0],[0,0,0],[0,0]],[[-6868800,18662400,1555200],[18662400,6220800,25600],[1555200,25600]],[[0,0,0],[0,0,0],[0,0]],[[32640000,66873600,1920000],[66873600,7680000,3200],[1920000,3200]],[[0,0,0],[0,0],[0]],[[311076800,141696000,1417600],[141696000,5670400],[1417600]],[[0,0,0],[0,0],[0]],[[1148326400,197424000,640000],[197424000,2560000],[640000]],[[0,0,0],[0,0],[0]],[[2623318400,190310400,172800],[190310400,691200],[172800]],[[0,0,0],[0,0],[0]],[[4177619200,130035200,25600],[130035200,102400],[25600]],[[0,0,0],[0,0],[0]],[[4886739200,63436800,1600],[63436800,6400],[1600]],[[0,0],[0]],[[4313811200,21936000],[21936000]],[[0,0],[0]],[[2913843200,5248000],[5248000]],[[0,0],[0]],[[1513792000,825600],[825600]],[[0,0],[0]],[[603633600,76800],[76800]],[[0,0],[0]],[[183014400,3200],[3200]],[[0]],[[41404800]],[[0]],[[6764800]],[[0]],[[753600]],[[0]],[[51200]],[[0]],[[1600]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
