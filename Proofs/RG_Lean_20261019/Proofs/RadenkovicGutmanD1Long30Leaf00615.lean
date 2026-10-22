/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00615 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20216098313812102961101275136000000000000 325249388723605103995582441468207300608 386436064465800318299406336000000000000))
theorem leaf00615_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20216098313812102961101275136000000000000 325249388723605103995582441468207300608 386436064465800318299406336000000000000 raw00615=true := by decide +kernel
#print axioms leaf00615_raw
theorem leaf00615_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00615=true := by decide +kernel
#print axioms leaf00615_rectangular
def affine00615 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00615 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00615_transform : affine00615=(NestedInteger.clearedAll 3 raw00615 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(67/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00615_transform
theorem leaf00615_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00615=true := by decide +kernel
#print axioms leaf00615_sign
theorem leaf00615_log : RationalLog.accepts (2345031/268435456) (-1272467811/536870912) 7 8=true := by decide +kernel
#print axioms leaf00615_log
def leaf00615 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (841664168103/1000000000000) (2345031/268435456) (-1272467811/536870912) 7 8 ![60,0,4] ![(67/3200),0,0] ![(3/6400),1,(1/16)] affine00615
theorem leaf00615_checked : FastNestedCellData.accepts 1 2 4 leaf00615=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (841664168103/1000000000000) (2345031/268435456) (-1272467811/536870912) 7 8 ![60,0,4] ![(67/3200),0,0] ![(3/6400),1,(1/16)] 20216098313812102961101275136000000000000 325249388723605103995582441468207300608 386436064465800318299406336000000000000 raw00615 affine00615
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00615_raw leaf00615_rectangular
    leaf00615_transform leaf00615_sign leaf00615_log
#print axioms leaf00615_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
