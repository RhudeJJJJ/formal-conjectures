/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode033
import Proofs.RadenkovicGutmanD18Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,7776],[0,7776,36]],[[0,0,0],[0,0,0],[0,0]],[[-26244,-17496,43740],[-17496,169128,24624],[43740,24624]],[[0,0,0],[0,0,0],[0,0]],[[-720252,664848,265356],[664848,1010880,26352],[265356,26352]],[[0,0,0],[0,0,0],[0,0]],[[-3103596,6537672,668736],[6537672,2503224,11304],[668736,11304]],[[0,0,0],[0,0,0],[0,0]],[[7364844,26208360,914328],[26208360,3360528,1872],[914328,1872]],[[0,0,0],[0,0,0],[0,0]],[[106536276,60520608,742392],[60520608,2681856,72],[742392,72]],[[0,0,0],[0,0],[0]],[[443026116,90801648,368208],[90801648,1310832],[368208]],[[0,0,0],[0,0],[0]],[[1095657480,93662568,110304],[93662568,388728],[110304]],[[0,0,0],[0,0],[0]],[[1861012872,68281704,18792],[68281704,66096],[18792]],[[0,0,0],[0,0],[0]],[[2304571320,35540280,1548],[35540280,5544],[1548]],[[0,0,0],[0,0],[0]],[[2144908800,13159368,36],[13159368,144],[36]],[[0,0],[0]],[[1524488112,3403080],[3403080]],[[0,0],[0]],[[833112288,591120],[591120]],[[0,0],[0]],[[349973604,63936],[63936]],[[0,0],[0]],[[112210596,3672],[3672]],[[0,0],[0]],[[27047304,72],[72]],[[0]],[[4774248]],[[0]],[[590580]],[[0]],[[47412]],[[0]],[[2124]],[[0]],[[36]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
