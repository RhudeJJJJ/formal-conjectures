/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[4900],[0],[0]],[[0,0],[0,0],[0]],[[147000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2023700,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[16944200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[96422200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[394773400,4900,0],[4900,0],[0]],[[0,0,0],[0,0],[0]],[[1200906700,107800,0],[107800,0],[0]],[[0,0,0],[0,0],[0]],[[2764197800,1053500,0],[1053500,0],[0]],[[0,0,0],[0,0],[0]],[[4857477800,6027000,0],[6027000,0],[0]],[[0,0,0],[0,0],[0]],[[6528181800,22397900,0],[22397900,0],[0]],[[0,0,0],[0,0],[0]],[[6677185900,56742000,1225],[56742000,2450],[1225]],[[0,0,0],[0,0],[0]],[[5134915800,100087400,17150],[100087400,34300],[17150]],[[0,0,0],[0,0],[0]],[[2905572600,123382000,99225],[123382000,198450],[99225]],[[0,0,0],[0,0],[0]],[[1167150600,105109900,306250],[105109900,612500],[306250]],[[0,0,0],[0,0],[0]],[[313154100,60123000,543900],[60123000,1087800],[543900]],[[0,0,0],[0,0],[0]],[[50009400,21829500,561050],[21829500,1122100],[561050]],[[0,0,0],[0,0],[0]],[[3572100,4498200,324625],[4498200,649250],[324625]],[[0,0,0],[0,0],[0]],[[0,396900,95550],[396900,191100],[95550]],[[0,0,0],[0,0],[0]],[[0,0,11025],[0,22050],[11025]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
