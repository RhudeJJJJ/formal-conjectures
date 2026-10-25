/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode112
import Proofs.RadenkovicGutmanD15Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,360],[0,360,736]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3240,11340],[3240,13248,15168],[11340,15168,4]],[[0,0,0],[0,0,0],[0,0]],[[147096,281232,155736],[281232,344712,38880],[155736,38880]],[[0,0,0],[0,0,0],[0,0]],[[4371516,3965112,642096],[3965112,1623488,35336],[642096,35336]],[[0,0,0],[0,0,0],[0,0]],[[49728600,22113120,1282800],[22113120,3499176,12912],[1282800,12912]],[[0,0,0],[0,0,0],[0,0]],[[298378164,67583592,1453848],[67583592,4234864,1656],[1453848,1656]],[[0,0,0],[0,0,0],[0,0]],[[1110178480,129914216,996496],[129914216,3097536,8],[996496,8]],[[0,0,0],[0,0],[0]],[[2804046644,168437608,420404],[168437608,1394608],[420404]],[[0,0,0],[0,0],[0]],[[5078063792,152947056,106768],[152947056,377768],[106768]],[[0,0,0],[0,0],[0]],[[6826453856,99107616,15028],[99107616,56656],[15028]],[[0,0,0],[0,0],[0]],[[6965643704,46056648,920],[46056648,3688],[920]],[[0,0,0],[0,0],[0]],[[5470144368,15226960,4],[15226960,16],[4]],[[0,0],[0]],[[3330378960,3496520],[3496520]],[[0,0],[0]],[[1574652792,530800],[530800]],[[0,0],[0]],[[575918304,48160],[48160]],[[0,0],[0]],[[161240020,2032],[2032]],[[0,0],[0]],[[33899664,8],[8]],[[0]],[[5181520]],[[0]],[[544608]],[[0]],[[35436]],[[0]],[[1112]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
