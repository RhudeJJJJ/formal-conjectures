/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode035
import Proofs.RadenkovicGutmanD34Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3468],[0,-3468]],[[0,0,0],[0,0,0],[0,0]],[[0,-31212,-31212],[-31212,-124848,-15028],[-31212,-15028]],[[0,0,0],[0,0,0],[0,0]],[[-561816,-1248480,-218484],[-1248480,-873936,-18496],[-218484,-18496]],[[0,0,0],[0,0,0],[0,0]],[[-13858128,-10404000,-603432],[-10404000,-2413728,-8092],[-603432,-8092]],[[0,0,0],[0,0,0],[0,0]],[[-123849216,-41169784,-875092],[-41169784,-3500368,-1156],[-875092,-1156]],[[0,0,0],[0,0],[0]],[[-601476048,-96209256,-735216],[-96209256,-2940864],[-735216]],[[0,0,0],[0,0],[0]],[[-1860186648,-146266368,-368764],[-146266368,-1475056],[-368764]],[[0,0,0],[0,0],[0]],[[-3975419264,-152048680,-108664],[-152048680,-434656],[-108664]],[[0,0,0],[0,0],[0]],[[-6157383136,-110833812,-17340],[-110833812,-69360],[-17340]],[[0,0,0],[0,0],[0]],[[-7117739384,-57149172,-1156],[-57149172,-4624],[-1156]],[[0,0],[0]],[[-6252149704,-20725924],[-20725924]],[[0,0],[0]],[[-4214792184,-5167320],[-5167320]],[[0,0],[0]],[[-2188076800,-842724],[-842724]],[[0,0],[0]],[[-872308352,-80920],[-80920]],[[0,0],[0]],[[-264458120,-3468],[-3468]],[[0]],[[-59829936]],[[0]],[[-9775136]],[[0]],[[-1088952]],[[0]],[[-73984]],[[0]],[[-2312]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
