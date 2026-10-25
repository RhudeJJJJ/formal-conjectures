/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-225]],[[0,0],[0,0,0],[0,0]],[[0,0,-2025],[0,0,-4050],[-2025,-4050]],[[0,0,0],[0,0,0],[0,0]],[[-18225,-36450,-35775],[-36450,-72900,-10800],[-35775,-10800]],[[0,0,0],[0,0,0],[0,0]],[[-643950,-741150,-156825],[-741150,-388800,-9900],[-156825,-9900]],[[0,0,0],[0,0,0],[0,0]],[[-8511075,-4629150,-321750],[-4629150,-874800,-3600],[-321750,-3600]],[[0,0,0],[0,0,0],[0,0]],[[-55661850,-14925600,-369900],[-14925600,-1080000,-450],[-369900,-450]],[[0,0,0],[0,0],[0]],[[-218281725,-29578950,-255600],[-29578950,-797400],[-255600]],[[0,0,0],[0,0],[0]],[[-570748500,-39093750,-108225],[-39093750,-360000],[-108225]],[[0,0,0],[0,0],[0]],[[-1058971950,-35954100,-27450],[-35954100,-97200],[-27450]],[[0,0,0],[0,0],[0]],[[-1449130050,-23497200,-3825],[-23497200,-14400],[-3825]],[[0,0,0],[0,0],[0]],[[-1498795200,-10977750,-225],[-10977750,-900],[-225]],[[0,0],[0]],[[-1189422000,-3638250],[-3638250]],[[0,0],[0]],[[-730116000,-834750],[-834750]],[[0,0],[0]],[[-347395950,-126000],[-126000]],[[0,0],[0]],[[-127642725,-11250],[-11250]],[[0,0],[0]],[[-35837100,-450],[-450]],[[0]],[[-7539750]],[[0]],[[-1149750]],[[0]],[[-119925]],[[0]],[[-7650]],[[0]],[[-225]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
