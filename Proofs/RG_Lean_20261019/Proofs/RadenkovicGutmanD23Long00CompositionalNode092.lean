/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode089
import Proofs.RadenkovicGutmanD23Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3174],[0,3174,-966]],[[0,0,0],[0,0,0],[0,0]],[[0,0,38088],[0,128547,-3496],[38088,-3496]],[[0,0,0],[0,0,0],[0,0]],[[121095,1043901,205482],[1043901,615618,-28842],[205482,-28842]],[[0,0,0],[0,0,0],[0,0]],[[8934327,9124974,424028],[9124974,995187,-34362],[424028,-34362]],[[0,0,0],[0,0,0],[0,0]],[[97252326,34771239,370530],[34771239,270710,-14076],[370530,-14076]],[[0,0,0],[0,0,0],[0,0]],[[509599983,75484988,18262],[75484988,-1101332,-1886],[18262,-1886]],[[0,0,0],[0,0],[0]],[[1628806801,102099001,-224618],[102099001,-1559722],[-224618]],[[0,0,0],[0,0],[0]],[[3510784078,87443470,-186576],[87443470,-960549],[-186576]],[[0,0,0],[0,0],[0]],[[5374143752,44178538,-69322],[44178538,-314318],[-69322]],[[0,0,0],[0,0],[0]],[[6003904613,8035188,-12650],[8035188,-53245],[-12650]],[[0,0,0],[0,0],[0]],[[4948690902,-5133853,-920],[-5133853,-3680],[-920]],[[0,0],[0]],[[2994479158,-4456618],[-4456618]],[[0,0],[0]],[[1292056464,-1623961],[-1623961]],[[0,0],[0]],[[362897657,-332672],[-332672]],[[0,0],[0]],[[42598277,-37329],[-37329]],[[0,0],[0]],[[-13222930,-1794],[-1794]],[[0]],[[-8050828]],[[0]],[[-2030509]],[[0]],[[-295803]],[[0]],[[-24265]],[[0]],[[-874]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
