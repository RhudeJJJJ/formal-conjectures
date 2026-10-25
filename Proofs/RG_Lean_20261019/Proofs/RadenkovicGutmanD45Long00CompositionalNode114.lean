/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,18225],[0,36450],[18225]],[[0,0,0],[0,0],[0]],[[0,656100,157950],[656100,315900],[157950]],[[0,0,0],[0,0],[0]],[[5904900,7435800,536625],[7435800,1073250],[536625]],[[0,0,0],[0,0],[0]],[[82668600,36085500,927450],[36085500,1854900],[927450]],[[0,0,0],[0,0],[0]],[[517662900,99387000,899100],[99387000,1798200],[899100]],[[0,0,0],[0,0],[0]],[[1929371400,173753100,506250],[173753100,1012500],[506250]],[[0,0,0],[0,0],[0]],[[4803089400,203958000,164025],[203958000,328050],[164025]],[[0,0,0],[0,0],[0]],[[8488330200,165450600,28350],[165450600,56700],[28350]],[[0,0,0],[0,0],[0]],[[11037797100,93798000,2025],[93798000,4050],[2025]],[[0,0],[0]],[[10791484200,37025100],[37025100]],[[0,0],[0]],[[8029708200,9963000],[9963000]],[[0,0],[0]],[[4569388200,1741500],[1741500]],[[0,0],[0]],[[1985172300,178200],[178200]],[[0,0],[0]],[[652584600,8100],[8100]],[[0]],[[159391800]],[[0]],[[28009800]],[[0]],[[3345300]],[[0]],[[243000]],[[0]],[[8100]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
