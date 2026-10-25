/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode071
import Proofs.RadenkovicGutmanD42Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-95256,0],[-95256,-18900,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1598940,-1789452,0],[-1789452,-228060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32681880,-14349636,0],[-14349636,-1113420,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-296452548,-65097396,0],[-65097396,-2853900,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1587235860,-186704028,0],[-186704028,-4202520,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5629614312,-358824396,0],[-358824396,-3695160,0],[0,0]],[[0,0,0],[0,0],[0]],[[-14076708324,-478399740,0],[-478399740,-1955100],[0]],[[0,0,0],[0,0],[0]],[[-25785468744,-451763424,0],[-451763424,-607740],[0]],[[0,0,0],[0,0],[0]],[[-35483118636,-305349072,0],[-305349072,-102060],[0]],[[0,0,0],[0,0],[0]],[[-37295552532,-147860412,0],[-147860412,-7140],[0]],[[0,0,0],[0,0],[0]],[[-30254141568,-50781948,0],[-50781948,0],[0]],[[0,0],[0]],[[-19040121912,-12059628],[-12059628]],[[0,0],[0]],[[-9299840508,-1881180],[-1881180]],[[0,0],[0]],[[-3508451184,-173292],[-173292]],[[0,0],[0]],[[-1011015348,-7140],[-7140]],[[0,0],[0]],[[-218163960,0],[0]],[[0]],[[-34092324]],[[0]],[[-3640728]],[[0]],[[-237552]],[[0]],[[-7140]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
