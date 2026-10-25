/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode035
import Proofs.RadenkovicGutmanD39Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4563],[0,-4563]],[[0,0,0],[0,0,0],[0,0]],[[0,-41067,-68445],[-41067,-219024,-20007],[-68445,-20007]],[[0,0,0],[0,0,0],[0,0]],[[-739206,-2548260,-526851],[-2548260,-1632852,-25350],[-526851,-25350]],[[0,0,0],[0,0,0],[0,0]],[[-25663716,-23875722,-1614834],[-23875722,-4847076,-11895],[-1614834,-11895]],[[0,0,0],[0,0,0],[0,0]],[[-264913740,-103138308,-2585349],[-103138308,-7554924,-2067],[-2585349,-2067]],[[0,0,0],[0,0,0],[0,0]],[[-1415585808,-260018538,-2377050],[-260018538,-6806904,-78],[-2377050,-78]],[[0,0,0],[0,0],[0]],[[-4717339614,-423206082,-1295307],[-423206082,-3660228],[-1295307]],[[0,0,0],[0,0],[0]],[[-10736217180,-468304668,-414258],[-468304668,-1164228],[-414258]],[[0,0,0],[0,0],[0]],[[-17575222080,-361836969,-72735],[-361836969,-205764],[-72735]],[[0,0,0],[0,0],[0]],[[-21359673114,-197230761,-5733],[-197230761,-16848],[-5733]],[[0,0,0],[0,0],[0]],[[-19651479042,-75566673,-78],[-75566673,-312],[-78]],[[0,0],[0]],[[-13839313722,-19957704],[-19957704]],[[0,0],[0]],[[-7493253768,-3480399],[-3480399]],[[0,0],[0]],[[-3113935188,-367146],[-367146]],[[0,0],[0]],[[-984882522,-19149],[-19149]],[[0,0],[0]],[[-233126400,-234],[-234]],[[0]],[[-40115088]],[[0]],[[-4775394]],[[0]],[[-359424]],[[0]],[[-14118]],[[0]],[[-156]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
