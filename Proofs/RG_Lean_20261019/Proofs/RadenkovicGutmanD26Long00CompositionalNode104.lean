/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode092
import Proofs.RadenkovicGutmanD26Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1872,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16848,-16848,0],[-16848,-15756,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-439452,-186732,0],[-186732,-51064,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4269564,-878904,0],[-878904,-81484,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22511424,-2320500,0],[-2320500,-68536,0],[0,0]],[[0,0,0],[0,0],[0]],[[-74773036,-3823768,0],[-3823768,-28912],[0]],[[0,0,0],[0,0],[0]],[[-169002756,-4121988,0],[-4121988,-3848],[0]],[[0,0,0],[0,0],[0]],[[-271671816,-2939248,0],[-2939248,1300],[0]],[[0,0,0],[0,0],[0]],[[-318533696,-1346488,0],[-1346488,520],[0]],[[0,0,0],[0,0],[0]],[[-275569684,-348608,0],[-348608,52],[0]],[[0,0],[0]],[[-175594952,-18148],[-18148]],[[0,0],[0]],[[-80731144,19240],[19240]],[[0,0],[0]],[[-25158640,6604],[6604]],[[0,0],[0]],[[-4218708,936],[936]],[[0,0],[0]],[[272012,52],[52]],[[0]],[[373464]],[[0]],[[106704]],[[0]],[[16484]],[[0]],[[1404]],[[0]],[[52]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
