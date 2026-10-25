/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode079
import Proofs.RadenkovicGutmanD29Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-45414,0],[-45414,-7569,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-749331,-658503,0],[-658503,-65598,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12239073,-4056984,0],[-4056984,-222865,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-88920612,-14057315,0],[-14057315,-385178,0],[0,0]],[[0,0,0],[0,0],[0]],[[-382020045,-30639312,0],[-30639312,-373404],[0]],[[0,0,0],[0,0],[0]],[[-1089203489,-44587297,0],[-44587297,-210250],[0]],[[0,0,0],[0,0],[0]],[[-2193137934,-44838756,0],[-44838756,-68121],[0]],[[0,0,0],[0,0],[0]],[[-3238788556,-31746068,0],[-31746068,-11774],[0]],[[0,0,0],[0,0],[0]],[[-3593541699,-15920130,0],[-15920130,-841],[0]],[[0,0],[0]],[[-3041168694,-5617039],[-5617039]],[[0,0],[0]],[[-1979520570,-1362420],[-1362420]],[[0,0],[0]],[[-993530488,-216137],[-216137]],[[0,0],[0]],[[-383249587,-20184],[-20184]],[[0,0],[0]],[[-112489637,-841],[-841]],[[0]],[[-24649710]],[[0]],[[-3902240]],[[0]],[[-421341]],[[0]],[[-27753]],[[0]],[[-841]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
