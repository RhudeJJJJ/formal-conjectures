/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode079
import Proofs.RadenkovicGutmanD40Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-86400,0],[-86400,-14400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1425600,-1252800,0],[-1252800,-124800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23284800,-7718400,0],[-7718400,-424000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-169171200,-26744000,0],[-26744000,-732800,0],[0,0]],[[0,0,0],[0,0],[0]],[[-726792000,-58291200,0],[-58291200,-710400],[0]],[[0,0,0],[0,0],[0]],[[-2072206400,-84827200,0],[-84827200,-400000],[0]],[[0,0,0],[0,0],[0]],[[-4172438400,-85305600,0],[-85305600,-129600],[0]],[[0,0,0],[0,0],[0]],[[-6161785600,-60396800,0],[-60396800,-22400],[0]],[[0,0,0],[0,0],[0]],[[-6836702400,-30288000,0],[-30288000,-1600],[0]],[[0,0],[0]],[[-5785814400,-10686400],[-10686400]],[[0,0],[0]],[[-3766032000,-2592000],[-2592000]],[[0,0],[0]],[[-1890188800,-411200],[-411200]],[[0,0],[0]],[[-729131200,-38400],[-38400]],[[0,0],[0]],[[-214011200,-1600],[-1600]],[[0]],[[-46896000]],[[0]],[[-7424000]],[[0]],[[-801600]],[[0]],[[-52800]],[[0]],[[-1600]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
