/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode096
import Proofs.RadenkovicGutmanD23Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3174],[0,3174,-966]],[[0,0,0],[0,0,0],[0,0]],[[0,0,38088],[0,130203,-3496],[38088,-3496]],[[0,0,0],[0,0,0],[0,0]],[[135999,1058805,205482],[1058805,629556,-28842],[205482,-28842]],[[0,0,0],[0,0,0],[0,0]],[[9323073,9290160,424028],[9290160,1040359,-34362],[424028,-34362]],[[0,0,0],[0,0,0],[0,0]],[[101029248,35548731,370530],[35548731,342792,-14076],[370530,-14076]],[[0,0,0],[0,0,0],[0,0]],[[529513935,77537738,18262],[77537738,-1040704,-1886],[18262,-1886]],[[0,0,0],[0,0],[0]],[[1694952179,105481565,-224618],[105481565,-1534146],[-224618]],[[0,0,0],[0,0],[0]],[[3660286516,91089844,-186576],[91089844,-957145],[-186576]],[[0,0,0],[0,0],[0]],[[5614468820,46778642,-69322],[46778642,-315468],[-69322]],[[0,0,0],[0,0],[0]],[[6285684421,9226312,-12650],[9226312,-53705],[-12650]],[[0,0,0],[0,0],[0]],[[5192464084,-4825469,-920],[-4825469,-3726],[-920]],[[0,0],[0]],[[3149813154,-4440564],[-4440564]],[[0,0],[0]],[[1363472476,-1640981],[-1640981]],[[0,0],[0]],[[385153377,-338514],[-338514]],[[0,0],[0]],[[46330211,-38157],[-38157]],[[0,0],[0]],[[-13463556,-1840],[-1840]],[[0]],[[-8381200]],[[0]],[[-2124901]],[[0]],[[-310385]],[[0]],[[-25507]],[[0]],[[-920]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
