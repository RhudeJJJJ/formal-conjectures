/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode078
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e078
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-36]],[[0,0],[0,0,0],[0,0]],[[0,0,-324],[0,-648,-648],[-324,-648]],[[0,0,0],[0,0,0],[0,0]],[[2916,-10692,-5724],[-10692,-17280,-1728],[-5724,-1728]],[[0,0,0],[0,0,0],[0,0]],[[-36936,-172044,-25092],[-172044,-81288,-1584],[-25092,-1584]],[[0,0,0],[0,0,0],[0,0]],[[-1041012,-991116,-51480],[-991116,-172944,-576],[-51480,-576]],[[0,0,0],[0,0,0],[0,0]],[[-8022456,-3050856,-59184],[-3050856,-204768,-72],[-59184,-72]],[[0,0,0],[0,0],[0]],[[-33380604,-5842188,-40896],[-5842188,-145584],[-40896]],[[0,0,0],[0,0],[0]],[[-89506800,-7499772,-17316],[-7499772,-63432],[-17316]],[[0,0,0],[0,0],[0]],[[-167964840,-6716880,-4392],[-6716880,-16560],[-4392]],[[0,0,0],[0,0],[0]],[[-231027048,-4281516,-612],[-4281516,-2376],[-612]],[[0,0,0],[0,0],[0]],[[-239478120,-1953252,-36],[-1953252,-144],[-36]],[[0,0],[0]],[[-190218960,-632736],[-632736]],[[0,0],[0]],[[-116803080,-142020],[-142020]],[[0,0],[0]],[[-55581768,-20988],[-20988]],[[0,0],[0]],[[-20422764,-1836],[-1836]],[[0,0],[0]],[[-5733936,-72],[-72]],[[0]],[[-1206360]],[[0]],[[-183960]],[[0]],[[-19188]],[[0]],[[-1224]],[[0]],[[-36]]]
theorem step082 : p082=NestedHorner.scale (-1) p078 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e078 p078 p082 rfl h078 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
