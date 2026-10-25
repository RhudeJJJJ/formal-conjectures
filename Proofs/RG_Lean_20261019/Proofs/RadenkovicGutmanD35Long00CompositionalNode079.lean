/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode033
import Proofs.RadenkovicGutmanD35Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3675],[0,3675]],[[0,0,0],[0,0,0],[0,0]],[[0,-33075,33075],[-33075,121275,15925],[33075,15925]],[[0,0,0],[0,0,0],[0,0]],[[-496125,363825,231525],[363825,830550,19600],[231525,19600]],[[0,0,0],[0,0,0],[0,0]],[[-3142125,5115600,639450],[5115600,2233175,8575],[639450,8575]],[[0,0,0],[0,0,0],[0,0]],[[1719900,23151275,927325],[23151275,3148250,1225],[927325,1225]],[[0,0,0],[0,0],[0]],[[80927175,57322650,779100],[57322650,2572500],[779100]],[[0,0,0],[0,0],[0]],[[384685525,90050975,390775],[90050975,1256850],[390775]],[[0,0,0],[0,0],[0]],[[1018183250,95812150,115150],[95812150,361375],[115150]],[[0,0,0],[0,0],[0]],[[1807291500,71208025,18375],[71208025,56350],[18375]],[[0,0,0],[0,0],[0]],[[2308236875,37371075,1225],[37371075,3675],[1225]],[[0,0],[0]],[[2195567500,13781250],[13781250]],[[0,0],[0]],[[1582998900,3491250],[3491250]],[[0,0],[0]],[[871504200,578200],[578200]],[[0,0],[0]],[[366134125,56350],[56350]],[[0,0],[0]],[[116390925,2450],[2450]],[[0]],[[27496350]],[[0]],[[4674600]],[[0]],[[540225]],[[0]],[[37975]],[[0]],[[1225]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
