/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode043
import Proofs.RadenkovicGutmanD17Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,867],[0,867,-510]],[[0,0,0],[0,0,0],[0,0]],[[0,7803,7803],[7803,32436,-5423],[7803,-5423]],[[0,0,0],[0,0,0],[0,0]],[[192780,323136,13311],[323136,63852,-19856],[13311,-19856]],[[0,0,0],[0,0,0],[0,0]],[[4470660,1982268,-69462],[1982268,-241808,-20417],[-69462,-20417]],[[0,0,0],[0,0,0],[0,0]],[[36015894,4949686,-276947],[4949686,-1045500,-7871],[-276947,-7871]],[[0,0,0],[0,0,0],[0,0]],[[155400060,4405074,-428196],[4405074,-1652400,-1020],[-428196,-1020]],[[0,0,0],[0,0],[0]],[[418639756,-5681672,-359669],[-5681672,-1404676],[-359669]],[[0,0,0],[0,0],[0]],[[751514784,-21492250,-176834],[-21492250,-696320],[-176834]],[[0,0,0],[0,0],[0]],[[911716868,-30175051,-50745],[-30175051,-201076],[-50745]],[[0,0,0],[0,0],[0]],[[708229214,-25586547,-7871],[-25586547,-31348],[-7871]],[[0,0,0],[0,0],[0]],[[250672106,-14417343,-510],[-14417343,-2040],[-510]],[[0,0],[0]],[[-145196490,-5532990],[-5532990]],[[0,0],[0]],[[-284949376,-1432879],[-1432879]],[[0,0],[0]],[[-223789496,-239938],[-239938]],[[0,0],[0]],[[-113371640,-23477],[-23477]],[[0,0],[0]],[[-40325700,-1020],[-1020]],[[0]],[[-10235020]],[[0]],[[-1824066]],[[0]],[[-217498]],[[0]],[[-15606]],[[0]],[[-510]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
