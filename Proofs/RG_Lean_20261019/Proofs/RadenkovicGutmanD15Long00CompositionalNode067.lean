/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode043
import Proofs.RadenkovicGutmanD15Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,2025],[0,4050,-2340],[2025,-2340,676]],[[0,0,0],[0,0,0],[0,0]],[[0,70065,-3510],[70065,-47502,2028],[-3510,2028]],[[0,0,0],[0,0,0],[0,0]],[[492156,235467,-33039],[235467,-237210,19968],[-33039,19968]],[[0,0,0],[0,0,0],[0,0]],[[3149712,-539541,-12078],[-539541,-206182,24284],[-12078,24284]],[[0,0,0],[0,0,0],[0,0]],[[1017522,-3902496,166512],[-3902496,549604,10036],[166512,10036]],[[0,0,0],[0,0,0],[0,0]],[[-53172114,-6968469,371370],[-6968469,1453788,1352],[371370,1352]],[[0,0,0],[0,0],[0]],[[-246917354,-1605673,368341],[-1605673,1482414],[368341]],[[0,0,0],[0,0],[0]],[[-586574120,13280300,200230],[13280300,809362],[200230]],[[0,0,0],[0,0],[0]],[[-867813818,25607791,61533],[25607791,248230],[61533]],[[0,0,0],[0,0],[0]],[[-818381552,25081097,10036],[25081097,40326],[10036]],[[0,0,0],[0,0],[0]],[[-427783508,15467800,676],[15467800,2704],[676]],[[0,0],[0]],[[11065670,6330345],[6330345]],[[0,0],[0]],[[230049130,1721765],[1721765]],[[0,0],[0]],[[218706302,299795],[299795]],[[0,0],[0]],[[121421926,30290],[30290]],[[0,0],[0]],[[45845076,1352],[1352]],[[0]],[[12161610]],[[0]],[[2244580]],[[0]],[[275468]],[[0]],[[20254]],[[0]],[[676]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
