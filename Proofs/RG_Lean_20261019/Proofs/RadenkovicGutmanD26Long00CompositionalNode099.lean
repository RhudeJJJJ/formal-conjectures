/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode096
import Proofs.RadenkovicGutmanD26Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4056],[0,4056,-1248]],[[0,0,0],[0,0,0],[0,0]],[[0,0,48672],[0,166140,-4732],[48672,-4732]],[[0,0,0],[0,0,0],[0,0]],[[172692,1350648,261300],[1350648,797316,-37596],[261300,-37596]],[[0,0,0],[0,0,0],[0,0]],[[11872224,11820276,534716],[11820276,1294228,-44616],[534716,-44616]],[[0,0,0],[0,0,0],[0,0]],[[128523564,45093204,456768],[45093204,360516,-18252],[456768,-18252]],[[0,0,0],[0,0,0],[0,0]],[[672717084,97972940,1924],[97972940,-1424488,-2444],[1924,-2444]],[[0,0,0],[0,0],[0]],[[2150030792,132528500,-303368],[132528500,-2029560],[-303368]],[[0,0,0],[0,0],[0]],[[4634723236,113332492,-246012],[113332492,-1253980],[-246012]],[[0,0,0],[0,0],[0]],[[7093631480,56888624,-90688],[56888624,-411372],[-90688]],[[0,0,0],[0,0],[0]],[[7919273908,9861748,-16484],[9861748,-69836],[-16484]],[[0,0,0],[0,0],[0]],[[6516223636,-7085000,-1196],[-7085000,-4836],[-1196]],[[0,0],[0]],[[3928931448,-5984472],[-5984472]],[[0,0],[0]],[[1682394064,-2169284],[-2169284]],[[0,0],[0]],[[463226868,-443664],[-443664]],[[0,0],[0]],[[48418448,-49764],[-49764]],[[0,0],[0]],[[-20272668,-2392],[-2392]],[[0]],[[-11363560]],[[0]],[[-2816164]],[[0]],[[-407264]],[[0]],[[-33280]],[[0]],[[-1196]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
