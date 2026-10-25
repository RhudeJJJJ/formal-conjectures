/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,147],[0,147]],[[0,0,0],[0,0,0],[0,0]],[[0,1323,2205],[1323,7056,679],[2205,679]],[[0,0,0],[0,0,0],[0,0]],[[23814,82404,17283],[82404,53844,966],[17283,966]],[[0,0,0],[0,0,0],[0,0]],[[832356,781578,54194],[781578,164836,567],[54194,567]],[[0,0,0],[0,0,0],[0,0]],[[8672076,3426052,89285],[3426052,267372,147],[89285,147]],[[0,0,0],[0,0,0],[0,0]],[[46834704,8785770,85274],[8785770,254072,14],[85274,14]],[[0,0,0],[0,0],[0]],[[157949022,14589890,49035],[14589890,147140],[49035]],[[0,0,0],[0,0],[0]],[[364358876,16540188,17010],[16540188,52164],[17010]],[[0,0,0],[0,0],[0]],[[605700928,13167721,3423],[13167721,10948],[3423]],[[0,0,0],[0,0],[0]],[[749301658,7455273,357],[7455273,1232],[357]],[[0,0,0],[0,0],[0]],[[703814146,3002321,14],[3002321,56],[14]],[[0,0],[0]],[[507970106,848904],[848904]],[[0,0],[0]],[[283282440,163471],[163471]],[[0,0],[0]],[[122060372,20202],[20202]],[[0,0],[0]],[[40396762,1421],[1421]],[[0,0],[0]],[[10138240,42],[42]],[[0]],[[1886864]],[[0]],[[250978]],[[0]],[[22400]],[[0]],[[1190]],[[0]],[[28]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
