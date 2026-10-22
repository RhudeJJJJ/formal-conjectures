/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00363 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4815956869607554693053022208000000000000 4138236086957491650729166209560686362624 61917360155134769613722615808000000000000))
theorem leaf00363_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4815956869607554693053022208000000000000 4138236086957491650729166209560686362624 61917360155134769613722615808000000000000 raw00363=true := by decide +kernel
#print axioms leaf00363_raw
theorem leaf00363_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00363=true := by decide +kernel
#print axioms leaf00363_rectangular
def affine00363 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00363 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00363_transform : affine00363=(NestedInteger.clearedAll 3 raw00363 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00363_transform
theorem leaf00363_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00363=true := by decide +kernel
#print axioms leaf00363_sign
theorem leaf00363_log : RationalLog.accepts (1729678373/2147483648) (-116158087/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00363_log
def leaf00363 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8354353441/125000000000) (1729678373/2147483648) (-116158087/1073741824) 1 8 ![60,0,4] ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)] affine00363
theorem leaf00363_checked : FastNestedCellData.accepts 1 2 4 leaf00363=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8354353441/125000000000) (1729678373/2147483648) (-116158087/1073741824) 1 8 ![60,0,4] ![(7/800),0,(1/4)] ![(1/6400),1,(1/4)] 4815956869607554693053022208000000000000 4138236086957491650729166209560686362624 61917360155134769613722615808000000000000 raw00363 affine00363
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00363_raw leaf00363_rectangular
    leaf00363_transform leaf00363_sign leaf00363_log
#print axioms leaf00363_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
