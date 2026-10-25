/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode033
import Proofs.RadenkovicGutmanD34Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3468],[0,3468,-2176]],[[0,0,0],[0,0,0],[0,0]],[[0,-31212,31212],[-31212,114444,-24140],[31212,-24140]],[[0,0,0],[0,0,0],[0,0]],[[-291924,343332,42228],[343332,78744,-85952],[42228,-85952]],[[0,0,0],[0,0,0],[0,0]],[[89964,1654848,-336600],[1654848,-1652740,-87652],[-336600,-87652]],[[0,0,0],[0,0,0],[0,0]],[[10964592,-3533620,-1239980],[-3533620,-5489368,-33660],[-1239980,-33660]],[[0,0,0],[0,0,0],[0,0]],[[31978428,-36854232,-1875984],[-36854232,-8017200,-4352],[-1875984,-4352]],[[0,0,0],[0,0],[0]],[[-60046924,-107727844,-1559172],[-107727844,-6525688],[-1559172]],[[0,0,0],[0,0],[0]],[[-600891384,-178081256,-761736],[-178081256,-3140580],[-761736]],[[0,0,0],[0,0],[0]],[[-1862219984,-191625020,-217668],[-191625020,-886856],[-217668]],[[0,0,0],[0,0],[0]],[[-3503340212,-141581780,-33660],[-141581780,-135796],[-33660]],[[0,0,0],[0,0],[0]],[[-4574066512,-73269048,-2176],[-73269048,-8704],[-2176]],[[0,0],[0]],[[-4372949168,-26538360],[-26538360]],[[0,0],[0]],[[-3140411360,-6591648],[-6591648]],[[0,0],[0]],[[-1713246060,-1069640],[-1069640]],[[0,0],[0]],[[-711106668,-102136],[-102136]],[[0,0],[0]],[[-222952008,-4352],[-4352]],[[0]],[[-51899232]],[[0]],[[-8690332]],[[0]],[[-989060]],[[0]],[[-68476]],[[0]],[[-2176]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
