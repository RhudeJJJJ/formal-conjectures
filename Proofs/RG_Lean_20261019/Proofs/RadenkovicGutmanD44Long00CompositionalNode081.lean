/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode079
import Proofs.RadenkovicGutmanD44Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-104544,0],[-104544,-17424,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1724976,-1515888,0],[-1515888,-151008,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28174608,-9339264,0],[-9339264,-513040,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-204697152,-32360240,0],[-32360240,-886688,0],[0,0]],[[0,0,0],[0,0],[0]],[[-879418320,-70532352,0],[-70532352,-859584],[0]],[[0,0,0],[0,0],[0]],[[-2507369744,-102640912,0],[-102640912,-484000],[0]],[[0,0,0],[0,0],[0]],[[-5048650464,-103219776,0],[-103219776,-156816],[0]],[[0,0,0],[0,0],[0]],[[-7455760576,-73080128,0],[-73080128,-27104],[0]],[[0,0,0],[0,0],[0]],[[-8272409904,-36648480,0],[-36648480,-1936],[0]],[[0,0],[0]],[[-7000835424,-12930544],[-12930544]],[[0,0],[0]],[[-4556898720,-3136320],[-3136320]],[[0,0],[0]],[[-2287128448,-497552],[-497552]],[[0,0],[0]],[[-882248752,-46464],[-46464]],[[0,0],[0]],[[-258953552,-1936],[-1936]],[[0]],[[-56744160]],[[0]],[[-8983040]],[[0]],[[-969936]],[[0]],[[-63888]],[[0]],[[-1936]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
