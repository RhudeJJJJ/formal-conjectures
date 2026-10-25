/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode051
import Proofs.RadenkovicGutmanD11Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,2904],[0,2904,22]],[[0,0,0],[0,0,0],[0,0]],[[-9801,6534,16335],[6534,65736,9350],[16335,9350]],[[0,0,0],[0,0,0],[0,0]],[[-50490,441342,99792],[441342,402600,10252],[99792,10252]],[[0,0,0],[0,0,0],[0,0]],[[2444607,3661812,253440],[3661812,1025420,4598],[253440,4598]],[[0,0,0],[0,0,0],[0,0]],[[29227506,14128532,349778],[14128532,1419264,836],[349778,836]],[[0,0,0],[0,0,0],[0,0]],[[154882211,32315844,287518],[32315844,1169608,44],[287518,44]],[[0,0,0],[0,0],[0]],[[497601522,48442130,145090],[48442130,591360],[145090]],[[0,0,0],[0,0],[0]],[[1086419422,50044984,44616],[50044984,182028],[44616]],[[0,0,0],[0,0],[0]],[[1708478728,36551658,7942],[36551658,32384],[7942]],[[0,0,0],[0,0],[0]],[[2001298156,19058666,715],[19058666,2904],[715]],[[0,0,0],[0,0],[0]],[[1781621864,7071108,22],[7071108,88],[22]],[[0,0],[0]],[[1218993820,1834360],[1834360]],[[0,0],[0]],[[643927240,320474],[320474]],[[0,0],[0]],[[262228659,35068],[35068]],[[0,0],[0]],[[81683426,2068],[2068]],[[0,0],[0]],[[19160262,44],[44]],[[0]],[[3295160]],[[0]],[[397375]],[[0]],[[31086]],[[0]],[[1353]],[[0]],[[22]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
