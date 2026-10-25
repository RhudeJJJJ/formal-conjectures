/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode033
import Proofs.RadenkovicGutmanD22Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,11616],[0,11616,44]],[[0,0,0],[0,0,0],[0,0]],[[-39204,-26136,65340],[-26136,252648,36608],[65340,36608]],[[0,0,0],[0,0,0],[0,0]],[[-1075140,993168,395604],[993168,1506912,38896],[395604,38896]],[[0,0,0],[0,0,0],[0,0]],[[-4622508,9751896,994752],[9751896,3722488,16456],[994752,16456]],[[0,0,0],[0,0,0],[0,0]],[[11043780,39036712,1356344],[39036712,4982032,2640],[1356344,2640]],[[0,0,0],[0,0,0],[0,0]],[[158947316,89998656,1097272],[89998656,3959296,88],[1097272,88]],[[0,0,0],[0,0],[0]],[[659903420,134776048,541376],[134776048,1923504],[541376]],[[0,0,0],[0,0],[0]],[[1629705352,138709208,160864],[138709208,565048],[160864]],[[0,0,0],[0,0],[0]],[[2764000184,100838056,27016],[100838056,94512],[27016]],[[0,0,0],[0,0],[0]],[[3417101336,52296376,2156],[52296376,7656],[2156]],[[0,0,0],[0,0],[0]],[[3174259616,19270152,44],[19270152,176],[44]],[[0,0],[0]],[[2250959568,4949560],[4949560]],[[0,0],[0]],[[1226718944,850960],[850960]],[[0,0],[0]],[[513549124,90464],[90464]],[[0,0],[0]],[[163934364,5016],[5016]],[[0,0],[0]],[[39285576,88],[88]],[[0]],[[6878872]],[[0]],[[840884]],[[0]],[[66220]],[[0]],[[2860]],[[0]],[[44]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
