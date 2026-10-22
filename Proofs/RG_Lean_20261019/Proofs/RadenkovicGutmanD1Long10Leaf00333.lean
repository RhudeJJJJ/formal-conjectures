/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00333 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 599065485440541747524403200000000000 202884476167876084154803869259399168 297895767408837595758592000000000000))
theorem leaf00333_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 599065485440541747524403200000000000 202884476167876084154803869259399168 297895767408837595758592000000000000 raw00333=true := by decide +kernel
#print axioms leaf00333_raw
theorem leaf00333_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00333=true := by decide +kernel
#print axioms leaf00333_rectangular
def affine00333 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00333 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/160),1,(1/4)]))
theorem leaf00333_transform : affine00333=(NestedInteger.clearedAll 3 raw00333 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00333_transform
theorem leaf00333_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00333=true := by decide +kernel
#print axioms leaf00333_sign
theorem leaf00333_log : RationalLog.accepts (422495/2097152) (-3440607999/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00333_log
def leaf00333 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (681058606279/1000000000000) (422495/2097152) (-3440607999/4294967296) 3 8 ![52,0,4] ![(1/8),0,0] ![(1/160),1,(1/4)] affine00333
theorem leaf00333_checked : FastNestedCellData.accepts 1 0 4 leaf00333=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (681058606279/1000000000000) (422495/2097152) (-3440607999/4294967296) 3 8 ![52,0,4] ![(1/8),0,0] ![(1/160),1,(1/4)] 599065485440541747524403200000000000 202884476167876084154803869259399168 297895767408837595758592000000000000 raw00333 affine00333
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00333_raw leaf00333_rectangular
    leaf00333_transform leaf00333_sign leaf00333_log
#print axioms leaf00333_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
