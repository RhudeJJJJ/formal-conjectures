/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode096
import Proofs.RadenkovicGutmanD11Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,726],[0,726,-198]],[[0,0,0],[0,0,0],[0,0]],[[0,0,8712],[0,30195,-352],[8712,-352]],[[0,0,0],[0,0,0],[0,0]],[[32967,246213,49170],[246213,156156,-5346],[49170,-5346]],[[0,0,0],[0,0,0],[0,0]],[[2202849,2212056,109076],[2212056,297583,-6666],[109076,-6666]],[[0,0,0],[0,0,0],[0,0]],[[24090264,8696259,113058],[8696259,209616,-2772],[113058,-2772]],[[0,0,0],[0,0,0],[0,0]],[[127784679,19615970,40414],[19615970,-77968,-374],[40414,-374]],[[0,0,0],[0,0],[0]],[[414632867,27959525,-23738],[27959525,-233970],[-23738]],[[0,0,0],[0,0],[0]],[[909481276,26030092,-29832],[26030092,-166705],[-29832]],[[0,0,0],[0,0],[0]],[[1421296580,15588914,-12298],[15588914,-58212],[-12298]],[[0,0,0],[0,0],[0]],[[1629136333,5373808,-2354],[5373808,-10241],[-2354]],[[0,0,0],[0,0],[0]],[[1389306556,450835,-176],[450835,-726],[-176]],[[0,0],[0]],[[883200978,-491172],[-491172]],[[0,0],[0]],[[413349244,-252989],[-252989]],[[0,0],[0]],[[137096553,-58674],[-58674]],[[0,0],[0]],[[28850723,-7029],[-7029]],[[0,0],[0]],[[2112132,-352],[-352]],[[0]],[[-811360]],[[0]],[[-315469]],[[0]],[[-53009]],[[0]],[[-4675]],[[0]],[[-176]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
