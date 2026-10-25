/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode096
import Proofs.RadenkovicGutmanD34Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6936],[0,6936,-2176]],[[0,0,0],[0,0,0],[0,0]],[[0,0,83232],[0,283356,-8908],[83232,-8908]],[[0,0,0],[0,0,0],[0,0]],[[291924,2302344,442884],[2302344,1341300,-66572],[442884,-66572]],[[0,0,0],[0,0,0],[0,0]],[[20173968,20054628,892364],[20054628,2104532,-78472],[892364,-78472]],[[0,0,0],[0,0,0],[0,0]],[[217993788,76082004,729504],[76082004,377332,-32028],[729504,-32028]],[[0,0,0],[0,0,0],[0,0]],[[1138232892,164111676,-62764],[164111676,-2727752,-4284],[-62764,-4284]],[[0,0,0],[0,0],[0]],[[3627571384,219645780,-569160],[219645780,-3683832],[-569160]],[[0,0,0],[0,0],[0]],[[7793948180,184335964,-444108],[184335964,-2239580],[-444108]],[[0,0,0],[0,0],[0]],[[11880654680,88370896,-161568],[88370896,-728892],[-161568]],[[0,0,0],[0,0],[0]],[[13193552916,10915428,-29172],[10915428,-123148],[-29172]],[[0,0,0],[0,0],[0]],[[10775612996,-14949528,-2108],[-14949528,-8500],[-2108]],[[0,0],[0]],[[6422067832,-11189944],[-11189944]],[[0,0],[0]],[[2692015824,-3932644],[-3932644]],[[0,0],[0]],[[702827668,-792880],[-792880]],[[0,0],[0]],[[49525216,-88196],[-88196]],[[0,0],[0]],[[-44131116,-4216],[-4216]],[[0]],[[-21447880]],[[0]],[[-5126724]],[[0]],[[-729232]],[[0]],[[-59024]],[[0]],[[-2108]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
