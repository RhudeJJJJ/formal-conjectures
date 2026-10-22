/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00112 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 337123599490746083506914538291200000000000 272919585947029757959400541215994540982272 2986725202431774783476378632192000000000000))
theorem leaf00112_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 337123599490746083506914538291200000000000 272919585947029757959400541215994540982272 2986725202431774783476378632192000000000000 raw00112=true := by decide +kernel
#print axioms leaf00112_raw
theorem leaf00112_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00112=true := by decide +kernel
#print axioms leaf00112_rectangular
def affine00112 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00112 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00112_transform : affine00112=(NestedInteger.clearedAll 3 raw00112 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00112_transform
theorem leaf00112_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00112=true := by decide +kernel
#print axioms leaf00112_sign
theorem leaf00112_log : RationalLog.accepts (3185887235/4294967296) (-641481585/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00112_log
def leaf00112 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (91377534741/1000000000000) (3185887235/4294967296) (-641481585/4294967296) 1 8 ![52,0,4] ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00112
theorem leaf00112_checked : FastNestedCellData.accepts 1 0 4 leaf00112=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (91377534741/1000000000000) (3185887235/4294967296) (-641481585/4294967296) 1 8 ![52,0,4] ![(19/1600),0,(1/4)] ![(1/1600),1,(1/4)] 337123599490746083506914538291200000000000 272919585947029757959400541215994540982272 2986725202431774783476378632192000000000000 raw00112 affine00112
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00112_raw leaf00112_rectangular
    leaf00112_transform leaf00112_sign leaf00112_log
#print axioms leaf00112_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
