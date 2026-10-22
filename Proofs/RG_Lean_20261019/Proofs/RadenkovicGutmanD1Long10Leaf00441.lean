/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00441 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 12014167274853115233522679808000000000000 13234838102576252110487048918019308781568 1847361957610080940046078181376000000000000))
theorem leaf00441_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 12014167274853115233522679808000000000000 13234838102576252110487048918019308781568 1847361957610080940046078181376000000000000 raw00441=true := by decide +kernel
#print axioms leaf00441_raw
theorem leaf00441_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00441=true := by decide +kernel
#print axioms leaf00441_rectangular
def affine00441 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00441 (IntegerComputedClassCell.leftNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/4),0,0] ![(1/64),1,(1/2)]))
theorem leaf00441_transform : affine00441=(NestedInteger.clearedAll 3 raw00441 (IntegerComputedClassCell.leftNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/4),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00441_transform
theorem leaf00441_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00441=true := by decide +kernel
#print axioms leaf00441_sign
theorem leaf00441_log : RationalLog.accepts (4697692087/4294967296) (192473379/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00441_log
def leaf00441 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (7164182443/1000000000000) (4697692087/4294967296) (192473379/4294967296) 0 8 ![52,0,4] ![(1/4),0,0] ![(1/64),1,(1/2)] affine00441
theorem leaf00441_checked : FastNestedCellData.accepts 1 0 4 leaf00441=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (7164182443/1000000000000) (4697692087/4294967296) (192473379/4294967296) 0 8 ![52,0,4] ![(1/4),0,0] ![(1/64),1,(1/2)] 12014167274853115233522679808000000000000 13234838102576252110487048918019308781568 1847361957610080940046078181376000000000000 raw00441 affine00441
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00441_raw leaf00441_rectangular
    leaf00441_transform leaf00441_sign leaf00441_log
#print axioms leaf00441_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
