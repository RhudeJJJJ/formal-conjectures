/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode071
import Proofs.RadenkovicGutmanD14Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-10584,0],[-10584,-2772,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-183708,-204876,0],[-204876,-31332,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3792096,-1664460,0],[-1664460,-144956,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34551468,-7582820,0],[-7582820,-356244,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-185226804,-21744212,0],[-21744212,-508648,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-656591376,-41700092,0],[-41700092,-437528,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1639226428,-55436052,0],[-55436052,-227948],[0]],[[0,0,0],[0,0],[0]],[[-2996529144,-52191104,0],[-52191104,-70084],[0]],[[0,0,0],[0,0],[0]],[[-4114164236,-35173600,0],[-35173600,-11676],[0]],[[0,0,0],[0,0],[0]],[[-4314357964,-16986396,0],[-16986396,-812],[0]],[[0,0,0],[0,0],[0]],[[-3491937904,-5819604,0],[-5819604,0],[0]],[[0,0],[0]],[[-2192899688,-1378972],[-1378972]],[[0,0],[0]],[[-1068924668,-214676],[-214676]],[[0,0],[0]],[[-402502408,-19740],[-19740]],[[0,0],[0]],[[-115784620,-812],[-812]],[[0,0],[0]],[[-24944360,0],[0]],[[0]],[[-3892196]],[[0]],[[-415072]],[[0]],[[-27048]],[[0]],[[-812]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
