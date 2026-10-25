/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,972],[0,972]],[[0,0,0],[0,0,0],[0,0]],[[0,8748,14580],[8748,46656,4320],[14580,4320]],[[0,0,0],[0,0,0],[0,0]],[[157464,543348,112752],[543348,349920,5652],[112752,5652]],[[0,0,0],[0,0,0],[0,0]],[[5476248,5106888,347652],[5106888,1047168,2844],[347652,2844]],[[0,0,0],[0,0,0],[0,0]],[[56663712,22144752,560844],[22144752,1649808,576],[560844,576]],[[0,0,0],[0,0,0],[0,0]],[[303621696,56078928,521028],[56078928,1508688,36],[521028,36]],[[0,0,0],[0,0],[0]],[[1014963048,91763712,288252],[91763712,829008],[288252]],[[0,0,0],[0,0],[0]],[[2318197752,102209904,94428],[102209904,272736],[94428]],[[0,0,0],[0,0],[0]],[[3810496896,79627356,17316],[79627356,51120],[17316]],[[0,0,0],[0,0],[0]],[[4653240840,43872192,1512],[43872192,4752],[1512]],[[0,0,0],[0,0],[0]],[[4305469104,17055360,36],[17055360,144],[36]],[[0,0],[0]],[[3052859904,4598892],[4598892]],[[0,0],[0]],[[1666872648,828036],[828036]],[[0,0],[0]],[[700014672,92340],[92340]],[[0,0],[0]],[[224424936,5436],[5436]],[[0,0],[0]],[[54094680,108],[108]],[[0]],[[9548496]],[[0]],[[1181160]],[[0]],[[94824]],[[0]],[[4248]],[[0]],[[72]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
