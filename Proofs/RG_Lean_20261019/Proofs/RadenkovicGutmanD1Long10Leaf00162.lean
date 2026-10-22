/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00162 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8410873129496445799183784345600000000000 78080885786144895693701796055971004416 178382455930563337027321856000000000000))
theorem leaf00162_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8410873129496445799183784345600000000000 78080885786144895693701796055971004416 178382455930563337027321856000000000000 raw00162=true := by decide +kernel
#print axioms leaf00162_raw
theorem leaf00162_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00162=true := by decide +kernel
#print axioms leaf00162_rectangular
def affine00162 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00162 (IntegerComputedClassCell.leftNumerator ![(7/320),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00162_transform : affine00162=(NestedInteger.clearedAll 3 raw00162 (IntegerComputedClassCell.leftNumerator ![(7/320),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/320),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00162_transform
theorem leaf00162_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00162=true := by decide +kernel
#print axioms leaf00162_sign
theorem leaf00162_log : RationalLog.accepts (27732585/4294967296) (-2707220577/1073741824) 8 8=true := by decide +kernel
#print axioms leaf00162_log
def leaf00162 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (54714521517/125000000000) (27732585/4294967296) (-2707220577/1073741824) 8 8 ![52,0,4] ![(7/320),0,0] ![(3/6400),1,(1/4)] affine00162
theorem leaf00162_checked : FastNestedCellData.accepts 1 0 4 leaf00162=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (54714521517/125000000000) (27732585/4294967296) (-2707220577/1073741824) 8 8 ![52,0,4] ![(7/320),0,0] ![(3/6400),1,(1/4)] 8410873129496445799183784345600000000000 78080885786144895693701796055971004416 178382455930563337027321856000000000000 raw00162 affine00162
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00162_raw leaf00162_rectangular
    leaf00162_transform leaf00162_sign leaf00162_log
#print axioms leaf00162_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
