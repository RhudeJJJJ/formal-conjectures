/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode033
import Proofs.RadenkovicGutmanD28Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,18816],[0,18816,56]],[[0,0,0],[0,0,0],[0,0]],[[-63504,-42336,105840],[-42336,409248,59024],[105840,59024]],[[0,0,0],[0,0,0],[0,0]],[[-1740312,1608768,639576],[1608768,2436000,62272],[639576,62272]],[[0,0,0],[0,0,0],[0,0]],[[-7466256,15774192,1604736],[15774192,6003424,25984],[1604736,25984]],[[0,0,0],[0,0,0],[0,0]],[[17954664,63054880,2182208],[63054880,8010688,4032],[2182208,4032]],[[0,0,0],[0,0,0],[0,0]],[[257156816,145144608,1759072],[145144608,6340096,112],[1759072,112]],[[0,0,0],[0,0],[0]],[[1065965096,216962368,863408],[216962368,3061632],[863408]],[[0,0,0],[0,0],[0]],[[2628892000,222801488,254464],[222801488,890848],[254464]],[[0,0,0],[0,0],[0]],[[4452182672,161524384,42112],[161524384,146496],[42112]],[[0,0,0],[0,0],[0]],[[5495262080,83470240,3248],[83470240,11424],[3248]],[[0,0,0],[0,0],[0]],[[5095129760,30608928,56],[30608928,224],[56]],[[0,0],[0]],[[3605005152,7808080],[7808080]],[[0,0],[0]],[[1959267968,1328320],[1328320]],[[0,0],[0]],[[817414864,138656],[138656]],[[0,0],[0]],[[259784616,7392],[7392]],[[0,0],[0]],[[61889184,112],[112]],[[0]],[[10747408]],[[0]],[[1297520]],[[0]],[[100072]],[[0]],[[4144]],[[0]],[[56]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
