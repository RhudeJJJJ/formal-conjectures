/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode113
import Proofs.RadenkovicGutmanD20Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0]],[[0,0,3600],[0,0,7200],[3600,7200]],[[0,0,0],[0,0,0],[0,0]],[[32400,64800,63600],[64800,129600,19200],[63600,19200]],[[0,0,0],[0,0,0],[0,0]],[[1144800,1317600,278800],[1317600,691200,17600],[278800,17600]],[[0,0,0],[0,0,0],[0,0]],[[15130800,8229600,572000],[8229600,1555200,6400],[572000,6400]],[[0,0,0],[0,0,0],[0,0]],[[98954400,26534400,657600],[26534400,1920000,800],[657600,800]],[[0,0,0],[0,0],[0]],[[388056400,52584800,454400],[52584800,1417600],[454400]],[[0,0,0],[0,0],[0]],[[1014664000,69500000,192400],[69500000,640000],[192400]],[[0,0,0],[0,0],[0]],[[1882616800,63918400,48800],[63918400,172800],[48800]],[[0,0,0],[0,0],[0]],[[2576231200,41772800,6800],[41772800,25600],[6800]],[[0,0,0],[0,0],[0]],[[2664524800,19516000,400],[19516000,1600],[400]],[[0,0],[0]],[[2114528000,6468000],[6468000]],[[0,0],[0]],[[1297984000,1484000],[1484000]],[[0,0],[0]],[[617592800,224000],[224000]],[[0,0],[0]],[[226920400,20000],[20000]],[[0,0],[0]],[[63710400,800],[800]],[[0]],[[13404000]],[[0]],[[2044000]],[[0]],[[213200]],[[0]],[[13600]],[[0]],[[400]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
