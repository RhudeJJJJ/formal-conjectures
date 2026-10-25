/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode071
import Proofs.RadenkovicGutmanD21Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-23814,0],[-23814,-5481,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-406539,-454167,0],[-454167,-63756,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8351343,-3666222,0],[-3666222,-302253,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-75926970,-16667847,0],[-16667847,-757512,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-406784637,-47800242,0],[-47800242,-1097544,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1442367087,-91765653,0],[-91765653,-954114,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3603718272,-122165526,0],[-122165526,-500829],[0]],[[0,0,0],[0,0],[0]],[[-6594278880,-115185420,0],[-115185420,-154812],[0]],[[0,0,0],[0,0],[0]],[[-9063824595,-77738934,0],[-77738934,-25893],[0]],[[0,0,0],[0,0],[0]],[[-9515596776,-37592247,0],[-37592247,-1806],[0]],[[0,0,0],[0,0],[0]],[[-7710197838,-12894798,0],[-12894798,0],[0]],[[0,0],[0]],[[-4847027388,-3058797],[-3058797]],[[0,0],[0]],[[-2365020315,-476658],[-476658]],[[0,0],[0]],[[-891371607,-43869],[-43869]],[[0,0],[0]],[[-256634616,-1806],[-1806]],[[0,0],[0]],[[-55332900,0],[0]],[[0]],[[-8640261]],[[0]],[[-922047]],[[0]],[[-60123]],[[0]],[[-1806]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
