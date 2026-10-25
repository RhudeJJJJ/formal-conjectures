/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode043
import Proofs.RadenkovicGutmanD18Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-972],[0,-972,576]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-8748,-14580],[-8748,-47952,9504],[-14580,9504,64]],[[0,0,0],[0,0,0],[0,0]],[[-215784,-593892,-34992],[-593892,-60624,38124],[-34992,38124]],[[0,0,0],[0,0,0],[0,0]],[[-7181784,-4159512,124092],[-4159512,710544,44004],[124092,44004]],[[0,0,0],[0,0,0],[0,0]],[[-67036464,-11740896,628020],[-11740896,2730176,19520],[628020,19520]],[[0,0,0],[0,0,0],[0,0]],[[-319401360,-13089888,1104444],[-13089888,4394320,3292],[1104444,3292]],[[0,0,0],[0,0,0],[0,0]],[[-932301096,9063888,1031556],[9063888,3895632,128],[1031556,128]],[[0,0,0],[0,0],[0]],[[-1798413224,50700608,560164],[50700608,2041968],[560164]],[[0,0,0],[0,0],[0]],[[-2342589344,79488068,178780],[79488068,636640],[178780]],[[0,0,0],[0,0],[0]],[[-1978777016,73028800,31896],[73028800,112384],[31896]],[[0,0,0],[0,0],[0]],[[-838375616,44225456,2716],[44225456,9696],[2716]],[[0,0,0],[0,0],[0]],[[283948864,18241732,64],[18241732,256],[64]],[[0,0],[0]],[[767643416,5115084],[5115084]],[[0,0],[0]],[[659034496,945884],[945884]],[[0,0],[0]],[[356709560,107444],[107444]],[[0,0],[0]],[[135059512,6404],[6404]],[[0,0],[0]],[[36638544,128],[128]],[[0]],[[7063176]],[[0]],[[934936]],[[0]],[[79112]],[[0]],[[3688]],[[0]],[[64]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
