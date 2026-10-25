/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode092
import Proofs.RadenkovicGutmanD23Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1656,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14904,-14904,0],[-14904,-13938,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-388746,-165186,0],[-165186,-45172,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3776922,-777492,0],[-777492,-72082,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19913952,-2052750,0],[-2052750,-60628,0],[0,0]],[[0,0,0],[0,0],[0]],[[-66145378,-3382564,0],[-3382564,-25576],[0]],[[0,0,0],[0,0],[0]],[[-149502438,-3646374,0],[-3646374,-3404],[0]],[[0,0,0],[0,0],[0]],[[-240325068,-2600104,0],[-2600104,1150],[0]],[[0,0,0],[0,0],[0]],[[-281779808,-1191124,0],[-1191124,460],[0]],[[0,0,0],[0,0],[0]],[[-243773182,-308384,0],[-308384,46],[0]],[[0,0],[0]],[[-155333996,-16054],[-16054]],[[0,0],[0]],[[-71416012,17020],[17020]],[[0,0],[0]],[[-22255720,5842],[5842]],[[0,0],[0]],[[-3731934,828],[828]],[[0,0],[0]],[[240626,46],[46]],[[0]],[[330372]],[[0]],[[94392]],[[0]],[[14582]],[[0]],[[1242]],[[0]],[[46]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
