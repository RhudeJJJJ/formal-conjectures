/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-6498,6498],[0,6498]],[[0,0,0],[0,0,0],[0,0]],[[29241,-58482,29241],[-58482,60648,17328],[29241,17328]],[[0,0,0],[0,0,0],[0,0]],[[-19494,-136458,155952],[-136458,432478,15884],[155952,15884]],[[0,0,0],[0,0,0],[0,0]],[[-1081917,994194,350892],[994194,1072892,5776],[350892,5776]],[[0,0,0],[0,0,0],[0,0]],[[-2978250,6229416,433200],[6229416,1412232,722],[433200,722]],[[0,0,0],[0,0],[0]],[[6268765,16482538,319846],[16482538,1098884],[319846]],[[0,0,0],[0,0],[0]],[[59479804,26363830,144400],[26363830,519118],[144400]],[[0,0,0],[0,0],[0]],[[185833414,28191212,38988],[28191212,145844],[38988]],[[0,0,0],[0,0],[0]],[[357322854,20978432,5776],[20978432,22382],[5776]],[[0,0,0],[0,0],[0]],[[480918424,11012666,361],[11012666,1444],[361]],[[0,0],[0]],[[476892552,4061250],[4061250]],[[0,0],[0]],[[356838392,1028850],[1028850]],[[0,0],[0]],[[203477650,170392],[170392]],[[0,0],[0]],[[88458357,16606],[16606]],[[0,0],[0]],[[29083604,722],[722]],[[0]],[[7103758]],[[0]],[[1248338]],[[0]],[[149093]],[[0]],[[10830]],[[0]],[[361]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
