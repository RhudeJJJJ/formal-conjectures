/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00239 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8922577483240873888520024883200000000000 6539221149785488908229229872942145339392 42247930607094024509511958528000000000000))
theorem leaf00239_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8922577483240873888520024883200000000000 6539221149785488908229229872942145339392 42247930607094024509511958528000000000000 raw00239=true := by decide +kernel
#print axioms leaf00239_raw
theorem leaf00239_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00239=true := by decide +kernel
#print axioms leaf00239_rectangular
def affine00239 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00239 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00239_transform : affine00239=(NestedInteger.clearedAll 3 raw00239 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00239_transform
theorem leaf00239_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00239=true := by decide +kernel
#print axioms leaf00239_sign
theorem leaf00239_log : RationalLog.accepts (2725809715/4294967296) (-976414495/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00239_log
def leaf00239 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (19347755783/125000000000) (2725809715/4294967296) (-976414495/4294967296) 1 8 ![52,0,4] ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00239
theorem leaf00239_checked : FastNestedCellData.accepts 1 0 4 leaf00239=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (19347755783/125000000000) (2725809715/4294967296) (-976414495/4294967296) 1 8 ![52,0,4] ![(71/1600),0,(1/2)] ![(3/3200),1,(1/2)] 8922577483240873888520024883200000000000 6539221149785488908229229872942145339392 42247930607094024509511958528000000000000 raw00239 affine00239
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00239_raw leaf00239_rectangular
    leaf00239_transform leaf00239_sign leaf00239_log
#print axioms leaf00239_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
