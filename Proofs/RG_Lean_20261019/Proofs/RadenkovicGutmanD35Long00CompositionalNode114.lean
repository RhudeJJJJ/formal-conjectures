/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,11025],[0,22050],[11025]],[[0,0,0],[0,0],[0]],[[0,396900,95550],[396900,191100],[95550]],[[0,0,0],[0,0],[0]],[[3572100,4498200,324625],[4498200,649250],[324625]],[[0,0,0],[0,0],[0]],[[50009400,21829500,561050],[21829500,1122100],[561050]],[[0,0,0],[0,0],[0]],[[313154100,60123000,543900],[60123000,1087800],[543900]],[[0,0,0],[0,0],[0]],[[1167150600,105109900,306250],[105109900,612500],[306250]],[[0,0,0],[0,0],[0]],[[2905572600,123382000,99225],[123382000,198450],[99225]],[[0,0,0],[0,0],[0]],[[5134915800,100087400,17150],[100087400,34300],[17150]],[[0,0,0],[0,0],[0]],[[6677185900,56742000,1225],[56742000,2450],[1225]],[[0,0],[0]],[[6528181800,22397900],[22397900]],[[0,0],[0]],[[4857477800,6027000],[6027000]],[[0,0],[0]],[[2764197800,1053500],[1053500]],[[0,0],[0]],[[1200906700,107800],[107800]],[[0,0],[0]],[[394773400,4900],[4900]],[[0]],[[96422200]],[[0]],[[16944200]],[[0]],[[2023700]],[[0]],[[147000]],[[0]],[[4900]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
