/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00406 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 277470940358240333932716779110400000000000 143669128608938005918426828114044179709952 477568505610039116053771976704000000000000))
theorem leaf00406_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 277470940358240333932716779110400000000000 143669128608938005918426828114044179709952 477568505610039116053771976704000000000000 raw00406=true := by decide +kernel
#print axioms leaf00406_raw
theorem leaf00406_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00406=true := by decide +kernel
#print axioms leaf00406_rectangular
def affine00406 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00406 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00406_transform : affine00406=(NestedInteger.clearedAll 3 raw00406 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00406_transform
theorem leaf00406_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00406=true := by decide +kernel
#print axioms leaf00406_sign
theorem leaf00406_log : RationalLog.accepts (1709557585/4294967296) (-1978282035/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00406_log
def leaf00406 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (150417298169/500000000000) (1709557585/4294967296) (-1978282035/4294967296) 2 8 ![60,0,4] ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)] affine00406
theorem leaf00406_checked : FastNestedCellData.accepts 1 2 4 leaf00406=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (150417298169/500000000000) (1709557585/4294967296) (-1978282035/4294967296) 2 8 ![60,0,4] ![(13/1280),0,(1/16)] ![(1/6400),1,(1/16)] 277470940358240333932716779110400000000000 143669128608938005918426828114044179709952 477568505610039116053771976704000000000000 raw00406 affine00406
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00406_raw leaf00406_rectangular
    leaf00406_transform leaf00406_sign leaf00406_log
#print axioms leaf00406_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
