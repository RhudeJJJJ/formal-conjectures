/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode217
import Proofs.RadenkovicGutmanD5Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-50],[0],[0]],[[0,0],[0,0],[0]],[[-1550,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-22050,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-190800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1122300,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-4750700,-75,0],[-75,0],[0]],[[0,0,0],[0,0],[0]],[[-14945450,-1675,0],[-1675,0],[0]],[[0,0,0],[0,0],[0]],[[-35584450,-16625,0],[-16625,0],[0]],[[0,0,0],[0,0],[0]],[[-64693200,-96650,0],[-96650,0],[0]],[[0,0,0],[0,0],[0]],[[-89948950,-365225,0],[-365225,0],[0]],[[0,0,0],[0,0],[0]],[[-95160150,-941475,-25],[-941475,-50],[-25]],[[0,0,0],[0,0],[0]],[[-75652900,-1690900,-350],[-1690900,-700],[-350]],[[0,0,0],[0,0],[0]],[[-44214900,-2123425,-2025],[-2123425,-4050],[-2025]],[[0,0,0],[0,0],[0]],[[-18320400,-1843075,-6250],[-1843075,-12500],[-6250]],[[0,0,0],[0,0],[0]],[[-5061150,-1073750,-11100],[-1073750,-22200],[-11100]],[[0,0,0],[0,0],[0]],[[-830250,-396675,-11450],[-396675,-22900],[-11450]],[[0,0,0],[0,0],[0]],[[-60750,-83025,-6625],[-83025,-13250],[-6625]],[[0,0,0],[0,0],[0]],[[0,-7425,-1950],[-7425,-3900],[-1950]],[[0,0,0],[0,0],[0]],[[0,0,-225],[0,-450],[-225]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
