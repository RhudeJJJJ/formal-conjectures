/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00388 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 76673126938058612284680306688000000000000 93052158142151090605153143131537001152512 349802592043859558072483577856000000000000))
theorem leaf00388_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 76673126938058612284680306688000000000000 93052158142151090605153143131537001152512 349802592043859558072483577856000000000000 raw00388=true := by decide +kernel
#print axioms leaf00388_raw
theorem leaf00388_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00388=true := by decide +kernel
#print axioms leaf00388_rectangular
def affine00388 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00388 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00388_transform : affine00388=(NestedInteger.clearedAll 3 raw00388 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/2),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00388_transform
theorem leaf00388_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00388=true := by decide +kernel
#print axioms leaf00388_sign
theorem leaf00388_log : RationalLog.accepts (4117227377/4294967296) (-90761223/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00388_log
def leaf00388 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (33251668319/125000000000) (4117227377/4294967296) (-90761223/4294967296) 1 8 ![52,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] affine00388
theorem leaf00388_checked : FastNestedCellData.accepts 1 0 4 leaf00388=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (33251668319/125000000000) (4117227377/4294967296) (-90761223/4294967296) 1 8 ![52,0,4] ![(1/2),0,(1/2)] ![(1/16),1,(1/4)] 76673126938058612284680306688000000000000 93052158142151090605153143131537001152512 349802592043859558072483577856000000000000 raw00388 affine00388
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00388_raw leaf00388_rectangular
    leaf00388_transform leaf00388_sign leaf00388_log
#print axioms leaf00388_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
