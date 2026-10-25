/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode051
import Proofs.RadenkovicGutmanD7Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,147],[0,147,-70]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1323,2205],[-1323,6615,-1001],[2205,-1001,-20]],[[0,0,0],[0,0,0],[0,0]],[[-14175,40257,7833],[40257,11736,-4574],[7833,-4574]],[[0,0,0],[0,0,0],[0,0]],[[146745,287568,-4126],[287568,-85641,-5713],[-4126,-5713]],[[0,0,0],[0,0,0],[0,0]],[[2026296,451805,-60475],[451805,-368420,-2833],[-60475,-2833]],[[0,0,0],[0,0,0],[0,0]],[[7098279,-1384928,-124146],[-1384928,-630096,-586],[-124146,-586]],[[0,0,0],[0,0,0],[0,0]],[[1498349,-7357283,-126025],[-7357283,-589326,-40],[-126025,-40]],[[0,0,0],[0,0],[0]],[[-63776296,-15353070,-73370],[-15353070,-326825],[-73370]],[[0,0,0],[0,0],[0]],[[-242691988,-19249731,-25297],[-19249731,-108992],[-25297]],[[0,0,0],[0,0],[0]],[[-504146649,-16066001,-5023],[-16066001,-21093],[-5023]],[[0,0,0],[0,0],[0]],[[-704799742,-9272250,-516],[-9272250,-2118],[-516]],[[0,0,0],[0,0],[0]],[[-711750564,-3740030,-20],[-3740030,-80],[-20]],[[0,0],[0]],[[-536384908,-1045142],[-1045142]],[[0,0],[0]],[[-306355527,-196364],[-196364]],[[0,0],[0]],[[-133273855,-23296],[-23296]],[[0,0],[0]],[[-44008860,-1532],[-1532]],[[0,0],[0]],[[-10897560,-40],[-40]],[[0]],[[-1976995]],[[0]],[[-252441]],[[0]],[[-21153]],[[0]],[[-1016]],[[0]],[[-20]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
