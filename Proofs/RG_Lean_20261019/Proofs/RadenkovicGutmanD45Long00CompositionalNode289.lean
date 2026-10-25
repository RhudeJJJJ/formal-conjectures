/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[8100],[0],[0]],[[0,0],[0,0],[0]],[[243000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3345300,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[28009800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[159391800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[652584600,8100,0],[8100,0],[0]],[[0,0,0],[0,0],[0]],[[1985172300,178200,0],[178200,0],[0]],[[0,0,0],[0,0],[0]],[[4569388200,1741500,0],[1741500,0],[0]],[[0,0,0],[0,0],[0]],[[8029708200,9963000,0],[9963000,0],[0]],[[0,0,0],[0,0],[0]],[[10791484200,37025100,0],[37025100,0],[0]],[[0,0,0],[0,0],[0]],[[11037797100,93798000,2025],[93798000,4050],[2025]],[[0,0,0],[0,0],[0]],[[8488330200,165450600,28350],[165450600,56700],[28350]],[[0,0,0],[0,0],[0]],[[4803089400,203958000,164025],[203958000,328050],[164025]],[[0,0,0],[0,0],[0]],[[1929371400,173753100,506250],[173753100,1012500],[506250]],[[0,0,0],[0,0],[0]],[[517662900,99387000,899100],[99387000,1798200],[899100]],[[0,0,0],[0,0],[0]],[[82668600,36085500,927450],[36085500,1854900],[927450]],[[0,0,0],[0,0],[0]],[[5904900,7435800,536625],[7435800,1073250],[536625]],[[0,0,0],[0,0],[0]],[[0,656100,157950],[656100,315900],[157950]],[[0,0,0],[0,0],[0]],[[0,0,18225],[0,36450],[18225]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
