/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode033
import Proofs.RadenkovicGutmanD34Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3468],[0,3468]],[[0,0,0],[0,0,0],[0,0]],[[0,-31212,31212],[-31212,114444,15028],[31212,15028]],[[0,0,0],[0,0,0],[0,0]],[[-468180,343332,218484],[343332,783768,18496],[218484,18496]],[[0,0,0],[0,0,0],[0,0]],[[-2965140,4827456,603432],[4827456,2107388,8092],[603432,8092]],[[0,0,0],[0,0,0],[0,0]],[[1623024,21847244,875092],[21847244,2970920,1156],[875092,1156]],[[0,0,0],[0,0],[0]],[[76368828,54093864,735216],[54093864,2427600],[735216]],[[0,0,0],[0,0],[0]],[[363017524,84978716,368764],[84978716,1186056],[368764]],[[0,0,0],[0,0],[0]],[[960832520,90415384,108664],[90415384,341020],[108664]],[[0,0,0],[0,0],[0]],[[1705493040,67197124,17340],[67197124,53176],[17340]],[[0,0,0],[0,0],[0]],[[2178221900,35266092,1156],[35266092,3468],[1156]],[[0,0],[0]],[[2071898800,13005000],[13005000]],[[0,0],[0]],[[1493834064,3294600],[3294600]],[[0,0],[0]],[[822415392,545632],[545632]],[[0,0],[0]],[[345511060,53176],[53176]],[[0,0],[0]],[[109835028,2312],[2312]],[[0]],[[25947576]],[[0]],[[4411296]],[[0]],[[509796]],[[0]],[[35836]],[[0]],[[1156]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
