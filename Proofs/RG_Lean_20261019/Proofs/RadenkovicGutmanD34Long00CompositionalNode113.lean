/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-20808,20808],[0,20808]],[[0,0,0],[0,0,0],[0,0]],[[93636,-187272,93636],[-187272,194208,55488],[93636,55488]],[[0,0,0],[0,0,0],[0,0]],[[-62424,-436968,499392],[-436968,1384888,50864],[499392,50864]],[[0,0,0],[0,0,0],[0,0]],[[-3464532,3183624,1123632],[3183624,3435632,18496],[1123632,18496]],[[0,0,0],[0,0,0],[0,0]],[[-9537000,19947936,1387200],[19947936,4522272,2312],[1387200,2312]],[[0,0,0],[0,0],[0]],[[20073940,52780648,1024216],[52780648,3518864],[1024216]],[[0,0,0],[0,0],[0]],[[190467184,84422680,462400],[84422680,1662328],[462400]],[[0,0,0],[0,0],[0]],[[595078744,90274352,124848],[90274352,467024],[124848]],[[0,0,0],[0,0],[0]],[[1144224984,67177472,18496],[67177472,71672],[18496]],[[0,0,0],[0,0],[0]],[[1540004704,35264936,1156],[35264936,4624],[1156]],[[0,0],[0]],[[1527112992,13005000],[13005000]],[[0,0],[0]],[[1142673632,3294600],[3294600]],[[0,0],[0]],[[651579400,545632],[545632]],[[0,0],[0]],[[283262772,53176],[53176]],[[0,0],[0]],[[93131984,2312],[2312]],[[0]],[[22747768]],[[0]],[[3997448]],[[0]],[[477428]],[[0]],[[34680]],[[0]],[[1156]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
