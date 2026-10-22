/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00327 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2191051280052439231229316825088000000000000 1678713402803274093477074913835064452186112 14133305229568589611300535926784000000000000))
theorem leaf00327_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2191051280052439231229316825088000000000000 1678713402803274093477074913835064452186112 14133305229568589611300535926784000000000000 raw00327=true := by decide +kernel
#print axioms leaf00327_raw
theorem leaf00327_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00327=true := by decide +kernel
#print axioms leaf00327_rectangular
def affine00327 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00327 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00327_transform : affine00327=(NestedInteger.clearedAll 3 raw00327 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00327_transform
theorem leaf00327_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00327=true := by decide +kernel
#print axioms leaf00327_sign
theorem leaf00327_log : RationalLog.accepts (2941306603/4294967296) (-406507973/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00327_log
def leaf00327 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (118777127893/1000000000000) (2941306603/4294967296) (-406507973/2147483648) 1 8 ![60,0,4] ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00327
theorem leaf00327_checked : FastNestedCellData.accepts 1 2 4 leaf00327=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (118777127893/1000000000000) (2941306603/4294967296) (-406507973/2147483648) 1 8 ![60,0,4] ![(49/6400),0,(1/8)] ![(1/6400),1,(1/8)] 2191051280052439231229316825088000000000000 1678713402803274093477074913835064452186112 14133305229568589611300535926784000000000000 raw00327 affine00327
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00327_raw leaf00327_rectangular
    leaf00327_transform leaf00327_sign leaf00327_log
#print axioms leaf00327_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
