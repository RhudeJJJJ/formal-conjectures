/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode073
import Proofs.RadenkovicGutmanD20Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1440,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12960,-99360,0],[-99360,-27240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1770120,-1402920,0],[-1402920,-170320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26739720,-8467920,0],[-8467920,-507880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-188172480,-28885400,0],[-28885400,-822160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-793389160,-62214160,0],[-62214160,-768160,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2233237240,-89714040,0],[-89714040,-422960],[0]],[[0,0,0],[0,0],[0]],[[-4454174960,-89580960,0],[-89580960,-135080],[0]],[[0,0,0],[0,0],[0]],[[-6529490240,-63066640,0],[-63066640,-23120],[0]],[[0,0,0],[0,0],[0]],[[-7201861720,-31482560,0],[-31482560,-1640],[0]],[[0,0,0],[0,0],[0]],[[-6065171440,-11066040,0],[-11066040,0],[0]],[[0,0],[0]],[[-3931740400,-2675600],[-2675600]],[[0,0],[0]],[[-1966493920,-423320],[-423320]],[[0,0],[0]],[[-756290840,-39440],[-39440]],[[0,0],[0]],[[-221403160,-1640],[-1640]],[[0,0],[0]],[[-48404400,0],[0]],[[0]],[[-7647200]],[[0]],[[-824200]],[[0]],[[-54200]],[[0]],[[-1640]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
