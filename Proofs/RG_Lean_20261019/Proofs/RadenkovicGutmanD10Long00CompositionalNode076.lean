/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode035
import Proofs.RadenkovicGutmanD10Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-900],[0,-1800],[-900]],[[0,0,0],[0,0],[0]],[[0,-29700,-7800],[-29700,-15600],[-7800]],[[0,0,0],[0,0],[0]],[[-243000,-332100,-26500],[-332100,-53000],[-26500]],[[0,0,0],[0,0],[0]],[[-3321000,-1586700,-45800],[-1586700,-91600],[-45800]],[[0,0,0],[0,0],[0]],[[-20244600,-4295000,-44400],[-4295000,-88800],[-44400]],[[0,0,0],[0,0],[0]],[[-73281600,-7372300,-25000],[-7372300,-50000],[-25000]],[[0,0,0],[0,0],[0]],[[-176859600,-8493700,-8100],[-8493700,-16200],[-8100]],[[0,0,0],[0,0],[0]],[[-302611600,-6763600,-1400],[-6763600,-2800],[-1400]],[[0,0,0],[0,0],[0]],[[-380640600,-3765900,-100],[-3765900,-200],[-100]],[[0,0],[0]],[[-359795800,-1460900],[-1460900]],[[0,0],[0]],[[-258772800,-386600],[-386600]],[[0,0],[0]],[[-142337800,-66500],[-66500]],[[0,0],[0]],[[-59781800,-6700],[-6700]],[[0,0],[0]],[[-19002800,-300],[-300]],[[0]],[[-4489200]],[[0]],[[-763200]],[[0]],[[-88200]],[[0]],[[-6200]],[[0]],[[-200]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
