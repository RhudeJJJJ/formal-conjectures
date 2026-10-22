/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00950 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25260649285803444014715764736000000000000 7165987639964854485358359723944599093248 9085080600162204838147391488000000000000))
theorem leaf00950_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25260649285803444014715764736000000000000 7165987639964854485358359723944599093248 9085080600162204838147391488000000000000 raw00950=true := by decide +kernel
#print axioms leaf00950_raw
theorem leaf00950_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00950=true := by decide +kernel
#print axioms leaf00950_rectangular
def affine00950 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00950 (IntegerComputedClassCell.leftNumerator ![(31/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/320),0,0] ![(1/320),1,(1/16)]))
theorem leaf00950_transform : affine00950=(NestedInteger.clearedAll 3 raw00950 (IntegerComputedClassCell.leftNumerator ![(31/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/320),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00950_transform
theorem leaf00950_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00950=true := by decide +kernel
#print axioms leaf00950_sign
theorem leaf00950_log : RationalLog.accepts (85142871/536870912) (-494304309/536870912) 3 8=true := by decide +kernel
#print axioms leaf00950_log
def leaf00950 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (788764344021/1000000000000) (85142871/536870912) (-494304309/536870912) 3 8 ![60,0,4] ![(31/320),0,0] ![(1/320),1,(1/16)] affine00950
theorem leaf00950_checked : FastNestedCellData.accepts 1 2 4 leaf00950=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (788764344021/1000000000000) (85142871/536870912) (-494304309/536870912) 3 8 ![60,0,4] ![(31/320),0,0] ![(1/320),1,(1/16)] 25260649285803444014715764736000000000000 7165987639964854485358359723944599093248 9085080600162204838147391488000000000000 raw00950 affine00950
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00950_raw leaf00950_rectangular
    leaf00950_transform leaf00950_sign leaf00950_log
#print axioms leaf00950_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
