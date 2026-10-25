/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode051
import Proofs.RadenkovicGutmanD21Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,10584],[0,10584,42]],[[0,0,0],[0,0,0],[0,0]],[[-35721,23814,59535],[23814,238896,33390],[59535,33390]],[[0,0,0],[0,0,0],[0,0]],[[-187110,1602342,360612],[1602342,1449000,35532],[360612,35532]],[[0,0,0],[0,0,0],[0,0]],[[8800407,13220172,907200],[13220172,3651060,15078],[907200,15078]],[[0,0,0],[0,0,0],[0,0]],[[105079086,50707692,1237698],[50707692,4989264,2436],[1237698,2436]],[[0,0,0],[0,0,0],[0,0]],[[555042411,115246404,1002078],[115246404,4045608,84],[1002078,84]],[[0,0,0],[0,0],[0]],[[1776530742,171534090,494970],[171534090,2000880],[494970]],[[0,0,0],[0,0],[0]],[[3862740462,175761264,147336],[175761264,596148],[147336]],[[0,0,0],[0,0],[0]],[[6047065248,127115898,24822],[127115898,100464],[24822]],[[0,0,0],[0,0],[0]],[[7048074516,65474346,1995],[65474346,8064],[1995]],[[0,0,0],[0,0],[0]],[[6239008104,23908668,42],[23908668,168],[42]],[[0,0],[0]],[[4240937820,6068160],[6068160]],[[0,0],[0]],[[2222976840,1026354],[1026354]],[[0,0],[0]],[[896773899,106428],[106428]],[[0,0],[0]],[[276045126,5628],[5628]],[[0,0],[0]],[[63750582,84],[84]],[[0]],[[10730160]],[[0]],[[1253175]],[[0]],[[92946]],[[0]],[[3633]],[[0]],[[42]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
