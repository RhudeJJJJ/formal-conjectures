/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode221
import Proofs.RadenkovicGutmanD35Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[2450,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[75950,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1080450,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[9349200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[54992700,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[232784300,3675,0],[3675,0],[0]],[[0,0,0],[0,0],[0]],[[732327050,82075,0],[82075,0],[0]],[[0,0,0],[0,0],[0]],[[1743638050,814625,0],[814625,0],[0]],[[0,0,0],[0,0],[0]],[[3169966800,4735850,0],[4735850,0],[0]],[[0,0,0],[0,0],[0]],[[4407498550,17896025,0],[17896025,0],[0]],[[0,0,0],[0,0],[0]],[[4662847350,46132275,1225],[46132275,2450],[1225]],[[0,0,0],[0,0],[0]],[[3706992100,82854100,17150],[82854100,34300],[17150]],[[0,0,0],[0,0],[0]],[[2166530100,104047825,99225],[104047825,198450],[99225]],[[0,0,0],[0,0],[0]],[[897699600,90310675,306250],[90310675,612500],[306250]],[[0,0,0],[0,0],[0]],[[247996350,52613750,543900],[52613750,1087800],[543900]],[[0,0,0],[0,0],[0]],[[40682250,19437075,561050],[19437075,1122100],[561050]],[[0,0,0],[0,0],[0]],[[2976750,4068225,324625],[4068225,649250],[324625]],[[0,0,0],[0,0],[0]],[[0,363825,95550],[363825,191100],[95550]],[[0,0,0],[0,0],[0]],[[0,0,11025],[0,22050],[11025]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
