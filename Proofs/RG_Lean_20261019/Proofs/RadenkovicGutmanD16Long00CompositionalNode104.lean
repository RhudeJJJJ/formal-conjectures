/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode092
import Proofs.RadenkovicGutmanD16Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1152,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10368,-10368,0],[-10368,-9696,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-270432,-114912,0],[-114912,-31424,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2627424,-540864,0],[-540864,-50144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13853184,-1428000,0],[-1428000,-42176,0],[0,0]],[[0,0,0],[0,0],[0]],[[-46014176,-2353088,0],[-2353088,-17792],[0]],[[0,0,0],[0,0],[0]],[[-104001696,-2536608,0],[-2536608,-2368],[0]],[[0,0,0],[0,0],[0]],[[-167182656,-1808768,0],[-1808768,800],[0]],[[0,0,0],[0,0],[0]],[[-196020736,-828608,0],[-828608,320],[0]],[[0,0,0],[0,0],[0]],[[-169581344,-214528,0],[-214528,32],[0]],[[0,0],[0]],[[-108058432,-11168],[-11168]],[[0,0],[0]],[[-49680704,11840],[11840]],[[0,0],[0]],[[-15482240,4064],[4064]],[[0,0],[0]],[[-2596128,576],[576]],[[0,0],[0]],[[167392,32],[32]],[[0]],[[229824]],[[0]],[[65664]],[[0]],[[10144]],[[0]],[[864]],[[0]],[[32]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
