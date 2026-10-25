/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode071
import Proofs.RadenkovicGutmanD6Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1944,0],[-1944,-756,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-35964,-39852,0],[-39852,-7956,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-755568,-331452,0],[-331452,-34428,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6938460,-1521252,0],[-1521252,-79812,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37278612,-4360932,0],[-4360932,-108744,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-132015072,-8331708,0],[-8331708,-90264,0],[0,0]],[[0,0,0],[0,0],[0]],[[-328687692,-11019876,0],[-11019876,-45804],[0]],[[0,0,0],[0,0],[0]],[[-598680600,-10319040,0],[-10319040,-13812],[0]],[[0,0,0],[0,0],[0]],[[-818697900,-6918144,0],[-6918144,-2268],[0]],[[0,0,0],[0,0],[0]],[[-855031836,-3324732,0],[-3324732,-156],[0]],[[0,0,0],[0,0],[0]],[[-689266128,-1133988,0],[-1133988,0],[0]],[[0,0],[0]],[[-431184648,-267612],[-267612]],[[0,0],[0]],[[-209413980,-41508],[-41508]],[[0,0],[0]],[[-78584952,-3804],[-3804]],[[0,0],[0]],[[-22533756,-156],[-156]],[[0,0],[0]],[[-4840200,0],[0]],[[0]],[[-753156]],[[0]],[[-80112]],[[0]],[[-5208]],[[0]],[[-156]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
