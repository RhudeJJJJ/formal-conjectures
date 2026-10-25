/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode051
import Proofs.RadenkovicGutmanD36Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,31104],[0,31104,72]],[[0,0,0],[0,0,0],[0,0]],[[-104976,69984,174960],[69984,701136,97200],[174960,97200]],[[0,0,0],[0,0,0],[0,0]],[[-554040,4700592,1055592],[4700592,4233600,101952],[1055592,101952]],[[0,0,0],[0,0,0],[0,0]],[[25715232,38681712,2643840],[38681712,10613520,42048],[2643840,42048]],[[0,0,0],[0,0,0],[0,0]],[[306858456,147960432,3587328],[147960432,14415264,6336],[3587328,6336]],[[0,0,0],[0,0,0],[0,0]],[[1618422336,335271744,2883168],[335271744,11596608,144],[2883168,144]],[[0,0,0],[0,0],[0]],[[5170932072,497339280,1409040],[497339280,5672160],[1409040]],[[0,0,0],[0,0],[0]],[[11221270272,507587184,412416],[507587184,1661328],[412416]],[[0,0,0],[0,0],[0]],[[17528916528,365347008,67392],[365347008,271584],[67392]],[[0,0,0],[0,0],[0]],[[20381479056,187043616,5040],[187043616,20304],[5040]],[[0,0,0],[0,0],[0]],[[17992462464,67753008,72],[67753008,288],[72]],[[0,0],[0]],[[12191296320,17001360],[17001360]],[[0,0],[0]],[[6365946240,2825424],[2825424]],[[0,0],[0]],[[2556012384,283968],[283968]],[[0,0],[0]],[[782059176,13968],[13968]],[[0,0],[0]],[[179157312,144],[144]],[[0]],[[29810160]],[[0]],[[3420000]],[[0]],[[245736]],[[0]],[[8928]],[[0]],[[72]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
