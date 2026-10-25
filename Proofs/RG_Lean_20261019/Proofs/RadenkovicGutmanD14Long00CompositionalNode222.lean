/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode221
import Proofs.RadenkovicGutmanD14Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[392,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12152,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[172872,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1495872,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[8798832,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[37245488,588,0],[588,0],[0]],[[0,0,0],[0,0],[0]],[[117172328,13132,0],[13132,0],[0]],[[0,0,0],[0,0],[0]],[[278982088,130340,0],[130340,0],[0]],[[0,0,0],[0,0],[0]],[[507194688,757736,0],[757736,0],[0]],[[0,0,0],[0,0],[0]],[[705199768,2863364,0],[2863364,0],[0]],[[0,0,0],[0,0],[0]],[[746055576,7381164,196],[7381164,392],[196]],[[0,0,0],[0,0],[0]],[[593118736,13256656,2744],[13256656,5488],[2744]],[[0,0,0],[0,0],[0]],[[346644816,16647652,15876],[16647652,31752],[15876]],[[0,0,0],[0,0],[0]],[[143631936,14449708,49000],[14449708,98000],[49000]],[[0,0,0],[0,0],[0]],[[39679416,8418200,87024],[8418200,174048],[87024]],[[0,0,0],[0,0],[0]],[[6509160,3109932,89768],[3109932,179536],[89768]],[[0,0,0],[0,0],[0]],[[476280,650916,51940],[650916,103880],[51940]],[[0,0,0],[0,0],[0]],[[0,58212,15288],[58212,30576],[15288]],[[0,0,0],[0,0],[0]],[[0,0,1764],[0,3528],[1764]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
