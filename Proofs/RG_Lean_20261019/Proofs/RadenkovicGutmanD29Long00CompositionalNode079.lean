/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode033
import Proofs.RadenkovicGutmanD29Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2523],[0,2523]],[[0,0,0],[0,0,0],[0,0]],[[0,-22707,22707],[-22707,83259,10933],[22707,10933]],[[0,0,0],[0,0,0],[0,0]],[[-340605,249777,158949],[249777,570198,13456],[158949,13456]],[[0,0,0],[0,0,0],[0,0]],[[-2157165,3512016,439002],[3512016,1533143,5887],[439002,5887]],[[0,0,0],[0,0,0],[0,0]],[[1180764,15894059,636637],[15894059,2161370,841],[636637,841]],[[0,0,0],[0,0],[0]],[[55558983,39353754,534876],[39353754,1766100],[534876]],[[0,0,0],[0,0],[0]],[[264098389,61822751,268279],[61822751,862866],[268279]],[[0,0,0],[0,0],[0]],[[699013970,65777974,79054],[65777974,248095],[79054]],[[0,0,0],[0,0],[0]],[[1240760940,48886489,12615],[48886489,38686],[12615]],[[0,0,0],[0,0],[0]],[[1584675275,25656387,841],[25656387,2523],[841]],[[0,0],[0]],[[1507324300,9461250],[9461250]],[[0,0],[0]],[[1086777204,2396850],[2396850]],[[0,0],[0]],[[598314312,396952],[396952]],[[0,0],[0]],[[251362285,38686],[38686]],[[0,0],[0]],[[79905933,1682],[1682]],[[0]],[[18877086]],[[0]],[[3209256]],[[0]],[[370881]],[[0]],[[26071]],[[0]],[[841]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
