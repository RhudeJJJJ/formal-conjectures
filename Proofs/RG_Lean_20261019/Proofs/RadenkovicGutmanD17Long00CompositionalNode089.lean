/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode033
import Proofs.RadenkovicGutmanD17Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,867],[0,867,-510]],[[0,0,0],[0,0,0],[0,0]],[[0,-7803,7803],[-7803,28611,-5423],[7803,-5423]],[[0,0,0],[0,0,0],[0,0]],[[-75735,85833,13311],[85833,30702,-19856],[13311,-19856]],[[0,0,0],[0,0,0],[0,0]],[[-25245,463284,-69462],[463284,-354433,-20417],[-69462,-20417]],[[0,0,0],[0,0,0],[0,0]],[[2595186,-486829,-276947],[-486829,-1240150,-7871],[-276947,-7871]],[[0,0,0],[0,0,0],[0,0]],[[8688207,-7792494,-428196],[-7792494,-1841100,-1020],[-428196,-1020]],[[0,0,0],[0,0],[0]],[[-8401349,-23920921,-359669],[-23920921,-1510926],[-359669]],[[0,0,0],[0,0],[0]],[[-125820910,-40325054,-176834],[-40325054,-730745],[-176834]],[[0,0,0],[0,0],[0]],[[-409809480,-43862159,-50745],[-43862159,-207026],[-50745]],[[0,0,0],[0,0],[0]],[[-787060645,-32632197,-7871],[-32632197,-31773],[-7871]],[[0,0,0],[0,0],[0]],[[-1039673420,-16969230,-510],[-16969230,-2040],[-510]],[[0,0],[0]],[[-1001568804,-6168450],[-6168450]],[[0,0],[0]],[[-723183672,-1536392],[-1536392]],[[0,0],[0]],[[-396143435,-249866],[-249866]],[[0,0],[0]],[[-164949453,-23902],[-23902]],[[0,0],[0]],[[-51848946,-1020],[-1020]],[[0]],[[-12094956]],[[0]],[[-2028831]],[[0]],[[-231251]],[[0]],[[-16031]],[[0]],[[-510]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
