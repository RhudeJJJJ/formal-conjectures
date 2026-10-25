/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode071
import Proofs.RadenkovicGutmanD29Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-45414,0],[-45414,-9657,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-768123,-858951,0],[-858951,-114492,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15735951,-6908670,0],[-6908670,-551261,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-142886538,-31372055,0],[-31372055,-1398264,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-765254349,-89973602,0],[-89973602,-2043688,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2713849551,-172832837,0],[-172832837,-1787618,0],[0,0]],[[0,0,0],[0,0],[0]],[[-6783446608,-230273862,0],[-230273862,-942413],[0]],[[0,0,0],[0,0],[0]],[[-12419858304,-217300364,0],[-217300364,-292204],[0]],[[0,0,0],[0,0],[0]],[[-17081867651,-146775670,0],[-146775670,-48981],[0]],[[0,0,0],[0,0],[0]],[[-17944816504,-71029671,0],[-71029671,-3422],[0]],[[0,0,0],[0,0],[0]],[[-14549263054,-24381054,0],[-24381054,0],[0]],[[0,0],[0]],[[-9151889948,-5787037],[-5787037]],[[0,0],[0]],[[-4468013963,-902306],[-902306]],[[0,0],[0]],[[-1684869463,-83085],[-83085]],[[0,0],[0]],[[-485326600,-3422],[-3422]],[[0,0],[0]],[[-104688260,0],[0]],[[0]],[[-16353941]],[[0]],[[-1745887]],[[0]],[[-113883]],[[0]],[[-3422]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
