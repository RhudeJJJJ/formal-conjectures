/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00434 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 206475678550619194432841318400000000000 236523647478939979344692256173595820032 17609383112543591292161386086400000000000))
theorem leaf00434_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 206475678550619194432841318400000000000 236523647478939979344692256173595820032 17609383112543591292161386086400000000000 raw00434=true := by decide +kernel
#print axioms leaf00434_raw
theorem leaf00434_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00434=true := by decide +kernel
#print axioms leaf00434_rectangular
def affine00434 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00434 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)]))
theorem leaf00434_transform : affine00434=(NestedInteger.clearedAll 3 raw00434 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(3/4)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00434_transform
theorem leaf00434_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00434=true := by decide +kernel
#print axioms leaf00434_sign
theorem leaf00434_log : RationalLog.accepts (1213699179/1073741824) (263116759/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00434_log
def leaf00434 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2686336551/200000000000) (1213699179/1073741824) (263116759/4294967296) 0 8 ![52,0,4] ![(5/16),0,(3/4)] ![(1/32),1,(1/4)] affine00434
theorem leaf00434_checked : FastNestedCellData.accepts 1 0 4 leaf00434=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2686336551/200000000000) (1213699179/1073741824) (263116759/4294967296) 0 8 ![52,0,4] ![(5/16),0,(3/4)] ![(1/32),1,(1/4)] 206475678550619194432841318400000000000 236523647478939979344692256173595820032 17609383112543591292161386086400000000000 raw00434 affine00434
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00434_raw leaf00434_rectangular
    leaf00434_transform leaf00434_sign leaf00434_log
#print axioms leaf00434_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
