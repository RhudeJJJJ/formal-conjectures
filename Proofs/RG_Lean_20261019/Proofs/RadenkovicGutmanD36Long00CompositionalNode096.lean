/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode043
import Proofs.RadenkovicGutmanD36Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3888],[0,3888,-2448]],[[0,0,0],[0,0,0],[0,0]],[[0,34992,34992],[34992,142560,-27216],[34992,-27216]],[[0,0,0],[0,0,0],[0,0]],[[851472,1423008,46656],[1423008,209088,-96768],[46656,-96768]],[[0,0,0],[0,0,0],[0,0]],[[19587744,8359200,-381024],[8359200,-1447776,-98640],[-381024,-98640]],[[0,0,0],[0,0,0],[0,0]],[[155422800,18885312,-1398384],[18885312,-5461632,-37872],[-1398384,-37872]],[[0,0,0],[0,0,0],[0,0]],[[657065952,9078048,-2113344],[9078048,-8325504,-4896],[-2113344,-4896]],[[0,0,0],[0,0],[0]],[[1721224656,-46636704,-1755504],[-46636704,-6950016],[-1755504]],[[0,0,0],[0,0],[0]],[[2961861696,-124344000,-857376],[-124344000,-3406176],[-857376]],[[0,0,0],[0,0],[0]],[[3331053216,-161035632,-244944],[-161035632,-975744],[-244944]],[[0,0,0],[0,0],[0]],[[2139449472,-131548464,-37872],[-131548464,-151200],[-37872]],[[0,0,0],[0,0],[0]],[[52041888,-72505872,-2448],[-72505872,-9792],[-2448]],[[0,0],[0]],[[-1501909920,-27414720],[-27414720]],[[0,0],[0]],[[-1800082944,-7022736],[-7022736]],[[0,0],[0]],[[-1252058400,-1166112],[-1166112]],[[0,0],[0]],[[-599709168,-113328],[-113328]],[[0,0],[0]],[[-206471808,-4896],[-4896]],[[0]],[[-51291360]],[[0]],[[-9002304]],[[0]],[[-1061136]],[[0]],[[-75456]],[[0]],[[-2448]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
