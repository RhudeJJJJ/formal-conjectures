/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00043 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 335840796043846889102265810944000000000 307137032051513468102299987108119445504 8435065502097746803428425728000000000000))
theorem leaf00043_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 335840796043846889102265810944000000000 307137032051513468102299987108119445504 8435065502097746803428425728000000000000 raw00043=true := by decide +kernel
#print axioms leaf00043_raw
theorem leaf00043_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00043=true := by decide +kernel
#print axioms leaf00043_rectangular
def affine00043 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00043 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)]))
theorem leaf00043_transform : affine00043=(NestedInteger.clearedAll 3 raw00043 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00043_transform
theorem leaf00043_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00043=true := by decide +kernel
#print axioms leaf00043_sign
theorem leaf00043_log : RationalLog.accepts (3789886375/4294967296) (-268667211/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00043_log
def leaf00043 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9102983017/250000000000) (3789886375/4294967296) (-268667211/4294967296) 1 8 ![52,0,4] ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)] affine00043
theorem leaf00043_checked : FastNestedCellData.accepts 1 0 4 leaf00043=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9102983017/250000000000) (3789886375/4294967296) (-268667211/4294967296) 1 8 ![52,0,4] ![(37/8000),0,(1/4)] ![(3/8000),1,(1/4)] 335840796043846889102265810944000000000 307137032051513468102299987108119445504 8435065502097746803428425728000000000000 raw00043 affine00043
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00043_raw leaf00043_rectangular
    leaf00043_transform leaf00043_sign leaf00043_log
#print axioms leaf00043_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
