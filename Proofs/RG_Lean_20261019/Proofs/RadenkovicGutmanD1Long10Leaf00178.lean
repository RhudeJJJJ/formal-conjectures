/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00178 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 869337976393513956002186133504000000000000 581797861780505635321013188311957777678336 3086335967807290999829153447936000000000000))
theorem leaf00178_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 869337976393513956002186133504000000000000 581797861780505635321013188311957777678336 3086335967807290999829153447936000000000000 raw00178=true := by decide +kernel
#print axioms leaf00178_raw
theorem leaf00178_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00178=true := by decide +kernel
#print axioms leaf00178_rectangular
def affine00178 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00178 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00178_transform : affine00178=(NestedInteger.clearedAll 3 raw00178 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00178_transform
theorem leaf00178_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00178=true := by decide +kernel
#print axioms leaf00178_sign
theorem leaf00178_log : RationalLog.accepts (2418473639/4294967296) (-616657815/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00178_log
def leaf00178 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (94253812263/500000000000) (2418473639/4294967296) (-616657815/2147483648) 1 8 ![52,0,4] ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00178
theorem leaf00178_checked : FastNestedCellData.accepts 1 0 4 leaf00178=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (94253812263/500000000000) (2418473639/4294967296) (-616657815/2147483648) 1 8 ![52,0,4] ![(41/1600),0,(1/4)] ![(3/3200),1,(1/4)] 869337976393513956002186133504000000000000 581797861780505635321013188311957777678336 3086335967807290999829153447936000000000000 raw00178 affine00178
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00178_raw leaf00178_rectangular
    leaf00178_transform leaf00178_sign leaf00178_log
#print axioms leaf00178_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
