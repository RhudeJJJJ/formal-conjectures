/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00406 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 134184736894119333365236629504000000000000 184718932616130828858272393264198483705856 1587113666207841421929547300864000000000000))
theorem leaf00406_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 134184736894119333365236629504000000000000 184718932616130828858272393264198483705856 1587113666207841421929547300864000000000000 raw00406=true := by decide +kernel
#print axioms leaf00406_raw
theorem leaf00406_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00406=true := by decide +kernel
#print axioms leaf00406_rectangular
def affine00406 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00406 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]))
theorem leaf00406_transform : affine00406=(NestedInteger.clearedAll 3 raw00406 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00406_transform
theorem leaf00406_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00406=true := by decide +kernel
#print axioms leaf00406_sign
theorem leaf00406_log : RationalLog.accepts (5296067311/4294967296) (449942035/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00406_log
def leaf00406 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)] affine00406
theorem leaf00406_checked : FastNestedCellData.accepts 1 0 4 leaf00406=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)] 134184736894119333365236629504000000000000 184718932616130828858272393264198483705856 1587113666207841421929547300864000000000000 raw00406 affine00406
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00406_raw leaf00406_rectangular
    leaf00406_transform leaf00406_sign leaf00406_log
#print axioms leaf00406_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
