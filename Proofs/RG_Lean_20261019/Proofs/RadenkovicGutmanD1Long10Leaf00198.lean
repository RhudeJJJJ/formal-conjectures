/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00198 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 160212869588049433855906545664000000000000 3753181803425582521531047261376836796416 6752147975057601028933287936000000000000))
theorem leaf00198_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 160212869588049433855906545664000000000000 3753181803425582521531047261376836796416 6752147975057601028933287936000000000000 raw00198=true := by decide +kernel
#print axioms leaf00198_raw
theorem leaf00198_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00198=true := by decide +kernel
#print axioms leaf00198_rectangular
def affine00198 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00198 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00198_transform : affine00198=(NestedInteger.clearedAll 3 raw00198 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00198_transform
theorem leaf00198_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00198=true := by decide +kernel
#print axioms leaf00198_sign
theorem leaf00198_log : RationalLog.accepts (64668729/4294967296) (-1126334121/536870912) 7 8=true := by decide +kernel
#print axioms leaf00198_log
def leaf00198 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (69481256507/125000000000) (64668729/4294967296) (-1126334121/536870912) 7 8 ![52,0,4] ![(103/3200),0,0] ![(3/3200),1,(1/4)] affine00198
theorem leaf00198_checked : FastNestedCellData.accepts 1 0 4 leaf00198=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (69481256507/125000000000) (64668729/4294967296) (-1126334121/536870912) 7 8 ![52,0,4] ![(103/3200),0,0] ![(3/3200),1,(1/4)] 160212869588049433855906545664000000000000 3753181803425582521531047261376836796416 6752147975057601028933287936000000000000 raw00198 affine00198
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00198_raw leaf00198_rectangular
    leaf00198_transform leaf00198_sign leaf00198_log
#print axioms leaf00198_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
