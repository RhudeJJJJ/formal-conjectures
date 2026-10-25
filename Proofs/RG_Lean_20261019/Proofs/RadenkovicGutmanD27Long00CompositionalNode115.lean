/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode113
import Proofs.RadenkovicGutmanD27Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,729]],[[0,0],[0,0,0],[0,0]],[[0,0,6561],[0,0,13122],[6561,13122]],[[0,0,0],[0,0,0],[0,0]],[[59049,118098,115911],[118098,236196,34992],[115911,34992]],[[0,0,0],[0,0,0],[0,0]],[[2086398,2401326,508113],[2401326,1259712,32076],[508113,32076]],[[0,0,0],[0,0,0],[0,0]],[[27575883,14998446,1042470],[14998446,2834352,11664],[1042470,11664]],[[0,0,0],[0,0,0],[0,0]],[[180344394,48358944,1198476],[48358944,3499200,1458],[1198476,1458]],[[0,0,0],[0,0],[0]],[[707232789,95835798,828144],[95835798,2583576],[828144]],[[0,0,0],[0,0],[0]],[[1849225140,126663750,350649],[126663750,1166400],[350649]],[[0,0,0],[0,0],[0]],[[3431069118,116491284,88938],[116491284,314928],[88938]],[[0,0,0],[0,0],[0]],[[4695181362,76130928,12393],[76130928,46656],[12393]],[[0,0,0],[0,0],[0]],[[4856096448,35567910,729],[35567910,2916],[729]],[[0,0],[0]],[[3853727280,11787930],[11787930]],[[0,0],[0]],[[2365575840,2704590],[2704590]],[[0,0],[0]],[[1125562878,408240],[408240]],[[0,0],[0]],[[413562429,36450],[36450]],[[0,0],[0]],[[116112204,1458],[1458]],[[0]],[[24428790]],[[0]],[[3725190]],[[0]],[[388557]],[[0]],[[24786]],[[0]],[[729]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
