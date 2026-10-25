/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,18225],[0,36450],[18225]],[[0,0,0],[0,0],[0]],[[0,601425,157950],[601425,315900],[157950]],[[0,0,0],[0,0],[0]],[[4920750,6725025,536625],[6725025,1073250],[536625]],[[0,0,0],[0,0],[0]],[[67250250,32130675,927450],[32130675,1854900],[927450]],[[0,0,0],[0,0],[0]],[[409953150,86973750,899100],[86973750,1798200],[899100]],[[0,0,0],[0,0],[0]],[[1483952400,149289075,506250],[149289075,1012500],[506250]],[[0,0,0],[0,0],[0]],[[3581406900,171997425,164025],[171997425,328050],[164025]],[[0,0,0],[0,0],[0]],[[6127884900,136962900,28350],[136962900,56700],[28350]],[[0,0,0],[0,0],[0]],[[7707972150,76259475,2025],[76259475,4050],[2025]],[[0,0],[0]],[[7285864950,29583225],[29583225]],[[0,0],[0]],[[5240149200,7828650],[7828650]],[[0,0],[0]],[[2882340450,1346625],[1346625]],[[0,0],[0]],[[1210581450,135675],[135675]],[[0,0],[0]],[[384806700,6075],[6075]],[[0]],[[90906300]],[[0]],[[15454800]],[[0]],[[1786050]],[[0]],[[125550]],[[0]],[[4050]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
