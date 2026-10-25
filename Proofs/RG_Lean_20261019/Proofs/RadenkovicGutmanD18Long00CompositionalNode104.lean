/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode092
import Proofs.RadenkovicGutmanD18Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1296,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11664,-11664,0],[-11664,-10908,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-304236,-129276,0],[-129276,-35352,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2955852,-608472,0],[-608472,-56412,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15584832,-1606500,0],[-1606500,-47448,0],[0,0]],[[0,0,0],[0,0],[0]],[[-51765948,-2647224,0],[-2647224,-20016],[0]],[[0,0,0],[0,0],[0]],[[-117001908,-2853684,0],[-2853684,-2664],[0]],[[0,0,0],[0,0],[0]],[[-188080488,-2034864,0],[-2034864,900],[0]],[[0,0,0],[0,0],[0]],[[-220523328,-932184,0],[-932184,360],[0]],[[0,0,0],[0,0],[0]],[[-190779012,-241344,0],[-241344,36],[0]],[[0,0],[0]],[[-121565736,-12564],[-12564]],[[0,0],[0]],[[-55890792,13320],[13320]],[[0,0],[0]],[[-17417520,4572],[4572]],[[0,0],[0]],[[-2920644,648],[648]],[[0,0],[0]],[[188316,36],[36]],[[0]],[[258552]],[[0]],[[73872]],[[0]],[[11412]],[[0]],[[972]],[[0]],[[36]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
