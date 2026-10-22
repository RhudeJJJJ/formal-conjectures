/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00409 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 43422274977621325927092846592000000000000 39826049402759397931503105833712748593152 1057436737795060635750845382656000000000000))
theorem leaf00409_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 43422274977621325927092846592000000000000 39826049402759397931503105833712748593152 1057436737795060635750845382656000000000000 raw00409=true := by decide +kernel
#print axioms leaf00409_raw
theorem leaf00409_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00409=true := by decide +kernel
#print axioms leaf00409_rectangular
def affine00409 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00409 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00409_transform : affine00409=(NestedInteger.clearedAll 3 raw00409 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00409_transform
theorem leaf00409_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00409=true := by decide +kernel
#print axioms leaf00409_sign
theorem leaf00409_log : RationalLog.accepts (3796280203/4294967296) (-132523647/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00409_log
def leaf00409 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9415704973/250000000000) (3796280203/4294967296) (-132523647/2147483648) 1 8 ![60,0,4] ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)] affine00409
theorem leaf00409_checked : FastNestedCellData.accepts 1 2 4 leaf00409=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9415704973/250000000000) (3796280203/4294967296) (-132523647/2147483648) 1 8 ![60,0,4] ![(13/1280),0,(1/2)] ![(1/6400),1,(1/2)] 43422274977621325927092846592000000000000 39826049402759397931503105833712748593152 1057436737795060635750845382656000000000000 raw00409 affine00409
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00409_raw leaf00409_rectangular
    leaf00409_transform leaf00409_sign leaf00409_log
#print axioms leaf00409_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
