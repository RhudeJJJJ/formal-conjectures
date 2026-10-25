/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode113
import Proofs.RadenkovicGutmanD18Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0]],[[0,0,2916],[0,0,5832],[2916,5832]],[[0,0,0],[0,0,0],[0,0]],[[26244,52488,51516],[52488,104976,15552],[51516,15552]],[[0,0,0],[0,0,0],[0,0]],[[927288,1067256,225828],[1067256,559872,14256],[225828,14256]],[[0,0,0],[0,0,0],[0,0]],[[12255948,6665976,463320],[6665976,1259712,5184],[463320,5184]],[[0,0,0],[0,0,0],[0,0]],[[80153064,21492864,532656],[21492864,1555200,648],[532656,648]],[[0,0,0],[0,0],[0]],[[314325684,42593688,368064],[42593688,1148256],[368064]],[[0,0,0],[0,0],[0]],[[821877840,56295000,155844],[56295000,518400],[155844]],[[0,0,0],[0,0],[0]],[[1524919608,51773904,39528],[51773904,139968],[39528]],[[0,0,0],[0,0],[0]],[[2086747272,33835968,5508],[33835968,20736],[5508]],[[0,0,0],[0,0],[0]],[[2158265088,15807960,324],[15807960,1296],[324]],[[0,0],[0]],[[1712767680,5239080],[5239080]],[[0,0],[0]],[[1051367040,1202040],[1202040]],[[0,0],[0]],[[500250168,181440],[181440]],[[0,0],[0]],[[183805524,16200],[16200]],[[0,0],[0]],[[51605424,648],[648]],[[0]],[[10857240]],[[0]],[[1655640]],[[0]],[[172692]],[[0]],[[11016]],[[0]],[[324]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
