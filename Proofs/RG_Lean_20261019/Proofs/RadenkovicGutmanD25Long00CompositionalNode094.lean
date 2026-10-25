/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode035
import Proofs.RadenkovicGutmanD25Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-5625],[0,-11250,3450],[-5625,3450]],[[0,0,0],[0,0,0],[0,0]],[[0,-154575,-17700],[-154575,26700,14950],[-17700,14950]],[[0,0,0],[0,0,0],[0,0]],[[-959850,-833625,51725],[-833625,538150,18400],[51725,18400]],[[0,0,0],[0,0,0],[0,0]],[[-6970050,433125,314050],[433125,1828700,8050],[314050,8050]],[[0,0,0],[0,0,0],[0,0]],[[-3322350,14112350,593050],[14112350,2927200,1150],[593050,1150]],[[0,0,0],[0,0],[0]],[[140344200,49633025,575150],[49633025,2613100],[575150]],[[0,0,0],[0,0],[0]],[[745159200,92421575,316225],[92421575,1366150],[316225]],[[0,0,0],[0,0],[0]],[[2063463100,108987000,99350],[108987000,414900],[99350]],[[0,0,0],[0,0],[0]],[[3746420650,86721675,16625],[86721675,67750],[16625]],[[0,0,0],[0,0],[0]],[[4832072350,47721925,1150],[47721925,4600],[1150]],[[0,0],[0]],[[4602369100,18202100],[18202100]],[[0,0],[0]],[[3303304850,4724875],[4724875]],[[0,0],[0]],[[1803083750,796475],[796475]],[[0,0],[0]],[[749013300,78625],[78625]],[[0,0],[0]],[[235028000,3450],[3450]],[[0]],[[54749400]],[[0]],[[9173150]],[[0]],[[1044550]],[[0]],[[72350]],[[0]],[[2300]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
