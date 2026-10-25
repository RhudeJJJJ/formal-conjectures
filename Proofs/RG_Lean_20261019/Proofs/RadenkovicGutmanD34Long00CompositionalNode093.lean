/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode033
import Proofs.RadenkovicGutmanD34Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,27744],[0,27744,68]],[[0,0,0],[0,0,0],[0,0]],[[-93636,-62424,156060],[-62424,603432,86768],[156060,86768]],[[0,0,0],[0,0,0],[0,0]],[[-2564892,2372112,941868],[2372112,3587136,91120],[941868,91120]],[[0,0,0],[0,0,0],[0,0]],[[-10988460,23237640,2359872],[23237640,8826808,37672],[2359872,37672]],[[0,0,0],[0,0,0],[0,0]],[[26536524,92803816,3203480],[92803816,11755024,5712],[3203480,5712]],[[0,0,0],[0,0,0],[0,0]],[[378877844,213405216,2576248],[213405216,9278464,136],[2576248,136]],[[0,0,0],[0,0],[0]],[[1568921636,318618352,1260176],[318618352,4462704],[1260176]],[[0,0,0],[0,0],[0]],[[3865816456,326720552,369376],[326720552,1290232],[369376]],[[0,0,0],[0,0],[0]],[[6540806984,236432872,60520],[236432872,209712],[60520]],[[0,0,0],[0,0],[0]],[[8064661688,121891768,4556],[121891768,15912],[4556]],[[0,0,0],[0,0],[0]],[[7468212608,44554824,68],[44554824,272],[68]],[[0,0],[0]],[[5276256816,11313160],[11313160]],[[0,0],[0]],[[2862383840,1910800],[1910800]],[[0,0],[0]],[[1191483556,196928],[196928]],[[0,0],[0]],[[377552388,10200],[10200]],[[0,0],[0]],[[89588232,136],[136]],[[0]],[[15469864]],[[0]],[[1851572]],[[0]],[[140692]],[[0]],[[5644]],[[0]],[[68]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
