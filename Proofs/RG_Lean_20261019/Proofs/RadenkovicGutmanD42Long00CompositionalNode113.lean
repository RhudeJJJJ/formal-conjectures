/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-31752,31752],[0,31752]],[[0,0,0],[0,0,0],[0,0]],[[142884,-285768,142884],[-285768,296352,84672],[142884,84672]],[[0,0,0],[0,0,0],[0,0]],[[-95256,-666792,762048],[-666792,2113272,77616],[762048,77616]],[[0,0,0],[0,0,0],[0,0]],[[-5286708,4858056,1714608],[4858056,5242608,28224],[1714608,28224]],[[0,0,0],[0,0,0],[0,0]],[[-14553000,30439584,2116800],[30439584,6900768,3528],[2116800,3528]],[[0,0,0],[0,0],[0]],[[30631860,80540712,1562904],[80540712,5369616],[1562904]],[[0,0,0],[0,0],[0]],[[290643696,128824920,705600],[128824920,2536632],[705600]],[[0,0,0],[0,0],[0]],[[908061336,137754288,190512],[137754288,712656],[190512]],[[0,0,0],[0,0],[0]],[[1746031896,102509568,28224],[102509568,109368],[28224]],[[0,0,0],[0,0],[0]],[[2349972576,53812584,1764],[53812584,7056],[1764]],[[0,0],[0]],[[2330300448,19845000],[19845000]],[[0,0],[0]],[[1743664608,5027400],[5027400]],[[0,0],[0]],[[994278600,832608],[832608]],[[0,0],[0]],[[432245268,81144],[81144]],[[0,0],[0]],[[142114896,3528],[3528]],[[0]],[[34711992]],[[0]],[[6099912]],[[0]],[[728532]],[[0]],[[52920]],[[0]],[[1764]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
