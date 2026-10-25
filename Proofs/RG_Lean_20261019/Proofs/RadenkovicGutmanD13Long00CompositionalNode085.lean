/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode073
import Proofs.RadenkovicGutmanD13Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-936,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8424,-44928,0],[-44928,-14430,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-826254,-626886,0],[-626886,-82316,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12083526,-3748212,0],[-3748212,-233662,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-83825664,-12691250,0],[-12691250,-367692,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-350357774,-27177956,0],[-27177956,-337688,0],[0,0]],[[0,0,0],[0,0],[0]],[[-980177250,-39015938,0],[-39015938,-183924],[0]],[[0,0,0],[0,0],[0]],[[-1945983988,-38820600,0],[-38820600,-58318],[0]],[[0,0,0],[0,0],[0]],[[-2842362432,-27253044,0],[-27253044,-9932],[0]],[[0,0,0],[0,0],[0]],[[-3125860322,-13573144,0],[-13573144,-702],[0]],[[0,0,0],[0,0],[0]],[[-2626088660,-4761770,0],[-4761770,0],[0]],[[0,0],[0]],[[-1698858980,-1149460],[-1149460]],[[0,0],[0]],[[-848203096,-181610],[-181610]],[[0,0],[0]],[[-325711698,-16900],[-16900]],[[0,0],[0]],[[-95224506,-702],[-702]],[[0,0],[0]],[[-20794020,0],[0]],[[0]],[[-3281720]],[[0]],[[-353366]],[[0]],[[-23218]],[[0]],[[-702]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
