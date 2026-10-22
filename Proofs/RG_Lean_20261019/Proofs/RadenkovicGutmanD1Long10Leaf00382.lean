/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00382 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 23077616738574210075551858688000000000000 26484542602962269896717299756416957939712 82695385783686809170019876864000000000000))
theorem leaf00382_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 23077616738574210075551858688000000000000 26484542602962269896717299756416957939712 82695385783686809170019876864000000000000 raw00382=true := by decide +kernel
#print axioms leaf00382_raw
theorem leaf00382_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00382=true := by decide +kernel
#print axioms leaf00382_rectangular
def affine00382 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00382 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf00382_transform : affine00382=(NestedInteger.clearedAll 3 raw00382 (IntegerComputedClassCell.leftNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/40),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00382_transform
theorem leaf00382_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00382=true := by decide +kernel
#print axioms leaf00382_sign
theorem leaf00382_log : RationalLog.accepts (3733359863/4294967296) (-150469199/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00382_log
def leaf00382 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (20016641763/62500000000) (3733359863/4294967296) (-150469199/2147483648) 1 8 ![52,0,4] ![(17/40),0,(1/4)] ![(3/80),1,(1/4)] affine00382
theorem leaf00382_checked : FastNestedCellData.accepts 1 0 4 leaf00382=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (20016641763/62500000000) (3733359863/4294967296) (-150469199/2147483648) 1 8 ![52,0,4] ![(17/40),0,(1/4)] ![(3/80),1,(1/4)] 23077616738574210075551858688000000000000 26484542602962269896717299756416957939712 82695385783686809170019876864000000000000 raw00382 affine00382
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00382_raw leaf00382_rectangular
    leaf00382_transform leaf00382_sign leaf00382_log
#print axioms leaf00382_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
