/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00016 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 79703237738305992503861444608000000000000 76341718596842608310637864836777077899264 4417186130276517788149383954432000000000000))
theorem leaf00016_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 79703237738305992503861444608000000000000 76341718596842608310637864836777077899264 4417186130276517788149383954432000000000000 raw00016=true := by decide +kernel
#print axioms leaf00016_raw
theorem leaf00016_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00016=true := by decide +kernel
#print axioms leaf00016_rectangular
def affine00016 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00016 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00016_transform : affine00016=(NestedInteger.clearedAll 3 raw00016 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00016_transform
theorem leaf00016_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00016=true := by decide +kernel
#print axioms leaf00016_sign
theorem leaf00016_log : RationalLog.accepts (4043934309/4294967296) (-129334137/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00016_log
def leaf00016 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (8641442351/500000000000) (4043934309/4294967296) (-129334137/4294967296) 1 8 ![52,0,4] ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)] affine00016
theorem leaf00016_checked : FastNestedCellData.accepts 1 0 4 leaf00016=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (8641442351/500000000000) (4043934309/4294967296) (-129334137/4294967296) 1 8 ![52,0,4] ![(7/3200),0,(1/4)] ![(3/16000),1,(1/4)] 79703237738305992503861444608000000000000 76341718596842608310637864836777077899264 4417186130276517788149383954432000000000000 raw00016 affine00016
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00016_raw leaf00016_rectangular
    leaf00016_transform leaf00016_sign leaf00016_log
#print axioms leaf00016_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
