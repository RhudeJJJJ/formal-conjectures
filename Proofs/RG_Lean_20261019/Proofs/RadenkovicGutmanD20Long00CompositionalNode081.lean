/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode079
import Proofs.RadenkovicGutmanD20Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-21600,0],[-21600,-3600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-356400,-313200,0],[-313200,-31200,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5821200,-1929600,0],[-1929600,-106000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-42292800,-6686000,0],[-6686000,-183200,0],[0,0]],[[0,0,0],[0,0],[0]],[[-181698000,-14572800,0],[-14572800,-177600],[0]],[[0,0,0],[0,0],[0]],[[-518051600,-21206800,0],[-21206800,-100000],[0]],[[0,0,0],[0,0],[0]],[[-1043109600,-21326400,0],[-21326400,-32400],[0]],[[0,0,0],[0,0],[0]],[[-1540446400,-15099200,0],[-15099200,-5600],[0]],[[0,0,0],[0,0],[0]],[[-1709175600,-7572000,0],[-7572000,-400],[0]],[[0,0],[0]],[[-1446453600,-2671600],[-2671600]],[[0,0],[0]],[[-941508000,-648000],[-648000]],[[0,0],[0]],[[-472547200,-102800],[-102800]],[[0,0],[0]],[[-182282800,-9600],[-9600]],[[0,0],[0]],[[-53502800,-400],[-400]],[[0]],[[-11724000]],[[0]],[[-1856000]],[[0]],[[-200400]],[[0]],[[-13200]],[[0]],[[-400]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
