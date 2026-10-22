/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00244 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 53998824148185096464524902400000000000 51651827789480019524077244128922959872 2757027766351026680772113203200000000000))
theorem leaf00244_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 53998824148185096464524902400000000000 51651827789480019524077244128922959872 2757027766351026680772113203200000000000 raw00244=true := by decide +kernel
#print axioms leaf00244_raw
theorem leaf00244_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00244=true := by decide +kernel
#print axioms leaf00244_rectangular
def affine00244 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00244 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00244_transform : affine00244=(NestedInteger.clearedAll 3 raw00244 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00244_transform
theorem leaf00244_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00244=true := by decide +kernel
#print axioms leaf00244_sign
theorem leaf00244_log : RationalLog.accepts (252046233/268435456) (-135287131/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00244_log
def leaf00244 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3746921117/200000000000) (252046233/268435456) (-135287131/4294967296) 1 8 ![60,0,4] ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)] affine00244
theorem leaf00244_checked : FastNestedCellData.accepts 1 2 4 leaf00244=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3746921117/200000000000) (252046233/268435456) (-135287131/4294967296) 1 8 ![60,0,4] ![(1/200),0,(1/2)] ![(1/6400),1,(1/2)] 53998824148185096464524902400000000000 51651827789480019524077244128922959872 2757027766351026680772113203200000000000 raw00244 affine00244
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00244_raw leaf00244_rectangular
    leaf00244_transform leaf00244_sign leaf00244_log
#print axioms leaf00244_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
