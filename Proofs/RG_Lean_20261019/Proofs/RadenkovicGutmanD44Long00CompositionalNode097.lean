/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode051
import Proofs.RadenkovicGutmanD44Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5808],[0,-5808]],[[0,0,0],[0,0,0],[0,0]],[[0,52272,-87120],[52272,-261360,-25432],[-87120,-25432]],[[0,0,0],[0,0,0],[0,0]],[[784080,-1727352,-670296],[-1727352,-1925352,-32120],[-670296,-32120]],[[0,0,0],[0,0,0],[0,0]],[[-4478760,-21031560,-2053304],[-21031560,-5641152,-14960],[-2053304,-14960]],[[0,0,0],[0,0,0],[0,0]],[[-132174504,-98736704,-3284864],[-98736704,-8682696,-2552],[-3284864,-2552]],[[0,0,0],[0,0,0],[0,0]],[[-919343568,-259637576,-3017080],[-259637576,-7730096,-88],[-3017080,-88]],[[0,0,0],[0,0],[0]],[[-3481223416,-434016880,-1641552],[-434016880,-4107136],[-1641552]],[[0,0,0],[0,0],[0]],[[-8564623144,-489545144,-523688],[-489545144,-1288672],[-523688]],[[0,0,0],[0,0],[0]],[[-14795972400,-383783136,-91520],[-383783136,-223432],[-91520]],[[0,0,0],[0,0],[0]],[[-18720141968,-211516888,-7128],[-211516888,-17600],[-7128]],[[0,0,0],[0,0],[0]],[[-17774520104,-81677464,-88],[-81677464,-264],[-88]],[[0,0],[0]],[[-12838696992,-21662256],[-21662256]],[[0,0],[0]],[[-7095532928,-3773792],[-3773792]],[[0,0],[0]],[[-2997311504,-393712],[-393712]],[[0,0],[0]],[[-959831752,-19712],[-19712]],[[0,0],[0]],[[-229047720,-176],[-176]],[[0]],[[-39518160]],[[0]],[[-4677200]],[[0]],[[-344168]],[[0]],[[-12584]],[[0]],[[-88]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
