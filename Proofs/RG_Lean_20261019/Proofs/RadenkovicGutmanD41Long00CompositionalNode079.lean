/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode033
import Proofs.RadenkovicGutmanD41Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5043],[0,5043]],[[0,0,0],[0,0,0],[0,0]],[[0,-45387,45387],[-45387,166419,21853],[45387,21853]],[[0,0,0],[0,0,0],[0,0]],[[-680805,499257,317709],[499257,1139718,26896],[317709,26896]],[[0,0,0],[0,0,0],[0,0]],[[-4311765,7019856,877482],[7019856,3064463,11767],[877482,11767]],[[0,0,0],[0,0,0],[0,0]],[[2360124,31769219,1272517],[31769219,4320170,1681],[1272517,1681]],[[0,0,0],[0,0],[0]],[[111051903,78660714,1069116],[78660714,3530100],[1069116]],[[0,0,0],[0,0],[0]],[[527882749,123571991,536239],[123571991,1724706],[536239]],[[0,0,0],[0,0],[0]],[[1397196770,131477734,158014],[131477734,495895],[158014]],[[0,0,0],[0,0],[0]],[[2480046540,97714849,25215],[97714849,77326],[25215]],[[0,0,0],[0,0],[0]],[[3167466275,51282267,1681],[51282267,5043],[1681]],[[0,0],[0]],[[3012856300,18911250],[18911250]],[[0,0],[0]],[[2172262164,4790850],[4790850]],[[0,0],[0]],[[1195917192,793432],[793432]],[[0,0],[0]],[[502425685,77326],[77326]],[[0,0],[0]],[[159716853,3362],[3362]],[[0]],[[37731726]],[[0]],[[6414696]],[[0]],[[741321]],[[0]],[[52111]],[[0]],[[1681]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
