/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[1600],[0],[0]],[[0,0],[0,0],[0]],[[48000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[660800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5532800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[31484800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[128905600,1600,0],[1600,0],[0]],[[0,0,0],[0,0],[0]],[[392132800,35200,0],[35200,0],[0]],[[0,0,0],[0,0],[0]],[[902595200,344000,0],[344000,0],[0]],[[0,0,0],[0,0],[0]],[[1586115200,1968000,0],[1968000,0],[0]],[[0,0,0],[0,0],[0]],[[2131651200,7313600,0],[7313600,0],[0]],[[0,0,0],[0,0],[0]],[[2180305600,18528000,400],[18528000,800],[400]],[[0,0,0],[0,0],[0]],[[1676707200,32681600,5600],[32681600,11200],[5600]],[[0,0,0],[0,0],[0]],[[948758400,40288000,32400],[40288000,64800],[32400]],[[0,0,0],[0,0],[0]],[[381110400,34321600,100000],[34321600,200000],[100000]],[[0,0,0],[0,0],[0]],[[102254400,19632000,177600],[19632000,355200],[177600]],[[0,0,0],[0,0],[0]],[[16329600,7128000,183200],[7128000,366400],[183200]],[[0,0,0],[0,0],[0]],[[1166400,1468800,106000],[1468800,212000],[106000]],[[0,0,0],[0,0],[0]],[[0,129600,31200],[129600,62400],[31200]],[[0,0,0],[0,0],[0]],[[0,0,3600],[0,7200],[3600]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
