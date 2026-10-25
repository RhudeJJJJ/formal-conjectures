/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode033
import Proofs.RadenkovicGutmanD45Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6075],[0,6075,-3870]],[[0,0,0],[0,0,0],[0,0]],[[0,-54675,54675],[-54675,200475,-43335],[54675,-43335]],[[0,0,0],[0,0,0],[0,0]],[[-506655,601425,69255],[601425,119070,-153360],[69255,-153360]],[[0,0,0],[0,0,0],[0,0]],[[239355,2813940,-614790],[2813940,-2995785,-156105],[-614790,-156105]],[[0,0,0],[0,0,0],[0,0]],[[19457010,-6869205,-2228715],[-6869205,-9842310,-59895],[-2228715,-59895]],[[0,0,0],[0,0,0],[0,0]],[[54829575,-66992670,-3356100],[-66992670,-14323500,-7740],[-3356100,-7740]],[[0,0,0],[0,0],[0]],[[-116508285,-193867425,-2782845],[-193867425,-11637630],[-2782845]],[[0,0,0],[0,0],[0]],[[-1094395230,-319135950,-1357650],[-319135950,-5594625],[-1357650]],[[0,0,0],[0,0],[0]],[[-3357587880,-342602055,-387585],[-342602055,-1578690],[-387585]],[[0,0,0],[0,0],[0]],[[-6288959565,-252745965,-59895],[-252745965,-241605],[-59895]],[[0,0,0],[0,0],[0]],[[-8190392940,-130656510,-3870],[-130656510,-15480],[-3870]],[[0,0],[0]],[[-7817236740,-47286450],[-47286450]],[[0,0],[0]],[[-5607208440,-11737800],[-11737800]],[[0,0],[0]],[[-3056242275,-1903770],[-1903770]],[[0,0],[0]],[[-1267637445,-181710],[-181710]],[[0,0],[0]],[[-397212930,-7740],[-7740]],[[0]],[[-92420460]],[[0]],[[-15469335]],[[0]],[[-1759995]],[[0]],[[-121815]],[[0]],[[-3870]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
