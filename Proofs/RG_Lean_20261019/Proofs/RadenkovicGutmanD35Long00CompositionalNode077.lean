/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,11025],[0,22050],[11025]],[[0,0,0],[0,0],[0]],[[0,363825,95550],[363825,191100],[95550]],[[0,0,0],[0,0],[0]],[[2976750,4068225,324625],[4068225,649250],[324625]],[[0,0,0],[0,0],[0]],[[40682250,19437075,561050],[19437075,1122100],[561050]],[[0,0,0],[0,0],[0]],[[247996350,52613750,543900],[52613750,1087800],[543900]],[[0,0,0],[0,0],[0]],[[897699600,90310675,306250],[90310675,612500],[306250]],[[0,0,0],[0,0],[0]],[[2166530100,104047825,99225],[104047825,198450],[99225]],[[0,0,0],[0,0],[0]],[[3706992100,82854100,17150],[82854100,34300],[17150]],[[0,0,0],[0,0],[0]],[[4662847350,46132275,1225],[46132275,2450],[1225]],[[0,0],[0]],[[4407498550,17896025],[17896025]],[[0,0],[0]],[[3169966800,4735850],[4735850]],[[0,0],[0]],[[1743638050,814625],[814625]],[[0,0],[0]],[[732327050,82075],[82075]],[[0,0],[0]],[[232784300,3675],[3675]],[[0]],[[54992700]],[[0]],[[9349200]],[[0]],[[1080450]],[[0]],[[75950]],[[0]],[[2450]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
