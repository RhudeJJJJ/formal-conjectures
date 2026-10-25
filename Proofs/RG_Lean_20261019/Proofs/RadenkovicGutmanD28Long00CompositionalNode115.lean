/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode113
import Proofs.RadenkovicGutmanD28Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0]],[[0,0,7056],[0,0,14112],[7056,14112]],[[0,0,0],[0,0,0],[0,0]],[[63504,127008,124656],[127008,254016,37632],[124656,37632]],[[0,0,0],[0,0,0],[0,0]],[[2243808,2582496,546448],[2582496,1354752,34496],[546448,34496]],[[0,0,0],[0,0,0],[0,0]],[[29656368,16130016,1121120],[16130016,3048192,12544],[1121120,12544]],[[0,0,0],[0,0,0],[0,0]],[[193950624,52007424,1288896],[52007424,3763200,1568],[1288896,1568]],[[0,0,0],[0,0],[0]],[[760590544,103066208,890624],[103066208,2778496],[890624]],[[0,0,0],[0,0],[0]],[[1988741440,136220000,377104],[136220000,1254400],[377104]],[[0,0,0],[0,0],[0]],[[3689928928,125280064,95648],[125280064,338688],[95648]],[[0,0,0],[0,0],[0]],[[5049413152,81874688,13328],[81874688,50176],[13328]],[[0,0,0],[0,0],[0]],[[5222468608,38251360,784],[38251360,3136],[784]],[[0,0],[0]],[[4144474880,12677280],[12677280]],[[0,0],[0]],[[2544048640,2908640],[2908640]],[[0,0],[0]],[[1210481888,439040],[439040]],[[0,0],[0]],[[444763984,39200],[39200]],[[0,0],[0]],[[124872384,1568],[1568]],[[0]],[[26271840]],[[0]],[[4006240]],[[0]],[[417872]],[[0]],[[26656]],[[0]],[[784]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
