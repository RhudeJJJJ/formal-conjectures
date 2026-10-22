/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00875 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15877700279751243767421079650304000000000000 2055504078237962716522603310027457203011584 2388088766361069339293553524736000000000000))
theorem leaf00875_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15877700279751243767421079650304000000000000 2055504078237962716522603310027457203011584 2388088766361069339293553524736000000000000 raw00875=true := by decide +kernel
#print axioms leaf00875_raw
theorem leaf00875_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00875=true := by decide +kernel
#print axioms leaf00875_rectangular
def affine00875 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00875 (IntegerComputedClassCell.leftNumerator ![(39/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/640),0,0] ![(1/640),1,(1/16)]))
theorem leaf00875_transform : affine00875=(NestedInteger.clearedAll 3 raw00875 (IntegerComputedClassCell.leftNumerator ![(39/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/640),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00875_transform
theorem leaf00875_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00875=true := by decide +kernel
#print axioms leaf00875_sign
theorem leaf00875_log : RationalLog.accepts (298818039/4294967296) (-715478325/536870912) 4 8=true := by decide +kernel
#print axioms leaf00875_log
def leaf00875 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (860731856869/1000000000000) (298818039/4294967296) (-715478325/536870912) 4 8 ![60,0,4] ![(39/640),0,0] ![(1/640),1,(1/16)] affine00875
theorem leaf00875_checked : FastNestedCellData.accepts 1 2 4 leaf00875=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (860731856869/1000000000000) (298818039/4294967296) (-715478325/536870912) 4 8 ![60,0,4] ![(39/640),0,0] ![(1/640),1,(1/16)] 15877700279751243767421079650304000000000000 2055504078237962716522603310027457203011584 2388088766361069339293553524736000000000000 raw00875 affine00875
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00875_raw leaf00875_rectangular
    leaf00875_transform leaf00875_sign leaf00875_log
#print axioms leaf00875_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
