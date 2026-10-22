/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00738 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2101272617317559503315475103744000000000 1326475007633781728030899383068421783552 5822458443595265608635121664000000000000))
theorem leaf00738_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2101272617317559503315475103744000000000 1326475007633781728030899383068421783552 5822458443595265608635121664000000000000 raw00738=true := by decide +kernel
#print axioms leaf00738_raw
theorem leaf00738_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00738=true := by decide +kernel
#print axioms leaf00738_rectangular
def affine00738 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00738 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00738_transform : affine00738=(NestedInteger.clearedAll 3 raw00738 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00738_transform
theorem leaf00738_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00738=true := by decide +kernel
#print axioms leaf00738_sign
theorem leaf00738_log : RationalLog.accepts (2208216625/4294967296) (-1428632233/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00738_log
def leaf00738 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56955108417/250000000000) (2208216625/4294967296) (-1428632233/4294967296) 1 8 ![60,0,4] ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00738
theorem leaf00738_checked : FastNestedCellData.accepts 1 2 4 leaf00738=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56955108417/250000000000) (2208216625/4294967296) (-1428632233/4294967296) 1 8 ![60,0,4] ![(103/3200),0,(1/4)] ![(3/6400),1,(1/4)] 2101272617317559503315475103744000000000 1326475007633781728030899383068421783552 5822458443595265608635121664000000000000 raw00738 affine00738
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00738_raw leaf00738_rectangular
    leaf00738_transform leaf00738_sign leaf00738_log
#print axioms leaf00738_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
