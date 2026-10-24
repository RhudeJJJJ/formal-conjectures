/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode035
import Proofs.RadenkovicGutmanD5Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-75],[0,-75]],[[0,0,0],[0,0,0],[0,0]],[[0,-675,-675],[-675,-2700,-325],[-675,-325]],[[0,0,0],[0,0,0],[0,0]],[[-12150,-27000,-4725],[-27000,-18900,-400],[-4725,-400]],[[0,0,0],[0,0,0],[0,0]],[[-299700,-225000,-13050],[-225000,-52200,-175],[-13050,-175]],[[0,0,0],[0,0,0],[0,0]],[[-2678400,-890350,-18925],[-890350,-75700,-25],[-18925,-25]],[[0,0,0],[0,0],[0]],[[-13007700,-2080650,-15900],[-2080650,-63600],[-15900]],[[0,0,0],[0,0],[0]],[[-40228950,-3163200,-7975],[-3163200,-31900],[-7975]],[[0,0,0],[0,0],[0]],[[-85973600,-3288250,-2350],[-3288250,-9400],[-2350]],[[0,0,0],[0,0],[0]],[[-133161400,-2396925,-375],[-2396925,-1500],[-375]],[[0,0,0],[0,0],[0]],[[-153930350,-1235925,-25],[-1235925,-100],[-25]],[[0,0],[0]],[[-135210850,-448225],[-448225]],[[0,0],[0]],[[-91150350,-111750],[-111750]],[[0,0],[0]],[[-47320000,-18225],[-18225]],[[0,0],[0]],[[-18864800,-1750],[-1750]],[[0,0],[0]],[[-5719250,-75],[-75]],[[0]],[[-1293900]],[[0]],[[-211400]],[[0]],[[-23550]],[[0]],[[-1600]],[[0]],[[-50]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
