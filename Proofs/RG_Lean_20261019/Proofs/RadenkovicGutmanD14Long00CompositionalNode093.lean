/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode033
import Proofs.RadenkovicGutmanD14Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,4704],[0,4704,28]],[[0,0,0],[0,0,0],[0,0]],[[-15876,-10584,26460],[-10584,102312,15008],[26460,15008]],[[0,0,0],[0,0,0],[0,0]],[[-436212,402192,161028],[402192,613536,16240],[161028,16240]],[[0,0,0],[0,0,0],[0,0]],[[-1886220,3963960,407232],[3963960,1525048,7112],[407232,7112]],[[0,0,0],[0,0,0],[0,0]],[[4428564,15927016,559160],[15927016,2057104,1232],[559160,1232]],[[0,0,0],[0,0,0],[0,0]],[[64574804,36871296,456568],[36871296,1652224,56],[456568,56]],[[0,0,0],[0,0],[0]],[[269213196,55480432,228256],[55480432,815024],[228256]],[[0,0,0],[0,0],[0]],[[667270856,57427832,69216],[57427832,245112],[69216]],[[0,0,0],[0,0],[0]],[[1135999704,42046312,12040],[42046312,42672],[12040]],[[0,0,0],[0,0],[0]],[[1410369688,22005368,1036],[22005368,3752],[1036]],[[0,0,0],[0,0],[0]],[[1316541408,8207304,28],[8207304,112],[28]],[[0,0],[0]],[[938997136,2143960],[2143960]],[[0,0],[0]],[[515313120,378000],[378000]],[[0,0],[0]],[[217599396,41888],[41888]],[[0,0],[0]],[[70227948,2520],[2520]],[[0,0],[0]],[[17073672,56],[56]],[[0]],[[3049144]],[[0]],[[383572]],[[0]],[[31612]],[[0]],[[1484]],[[0]],[[28]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
