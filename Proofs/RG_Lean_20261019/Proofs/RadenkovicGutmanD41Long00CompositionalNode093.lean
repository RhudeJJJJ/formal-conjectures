/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode033
import Proofs.RadenkovicGutmanD41Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,40344],[0,40344,82]],[[0,0,0],[0,0,0],[0,0]],[[-136161,-90774,226935],[-90774,877482,125870],[226935,125870]],[[0,0,0],[0,0,0],[0,0]],[[-3728376,3449412,1368252],[3449412,5210772,131692],[1368252,131692]],[[0,0,0],[0,0,0],[0,0]],[[-15955191,33766452,3424320],[33766452,12806350,54038],[3424320,54038]],[[0,0,0],[0,0,0],[0,0]],[[38660622,134753962,4641938],[134753962,17027956,8036],[4641938,8036]],[[0,0,0],[0,0,0],[0,0]],[[550601669,309618060,3725998],[309618060,13411264,164],[3725998,164]],[[0,0,0],[0,0],[0]],[[2278168608,461824492,1817530],[461824492,6429620],[1817530]],[[0,0,0],[0,0],[0]],[[5609369162,473018312,530376],[473018312,1849182],[530376]],[[0,0,0],[0,0],[0]],[[9483649320,341801338,86182],[341801338,297660],[86182]],[[0,0,0],[0,0],[0]],[[11683165906,175877126,6355],[175877126,22058],[6355]],[[0,0,0],[0,0],[0]],[[10808355876,64120146,82],[64120146,328],[82]],[[0,0],[0]],[[7626963664,16219600],[16219600]],[[0,0],[0]],[[4131596568,2723220],[2723220]],[[0,0],[0]],[[1716625761,277652],[277652]],[[0,0],[0]],[[542649432,14022],[14022]],[[0,0],[0]],[[128343858,164],[164]],[[0]],[[22058656]],[[0]],[[2621089]],[[0]],[[196636]],[[0]],[[7667]],[[0]],[[82]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
