/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00422 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 138507161493559821991936000000000000 170739973317662440273242751277989888 5421541643466941170450432000000000000))
theorem leaf00422_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 138507161493559821991936000000000000 170739973317662440273242751277989888 5421541643466941170450432000000000000 raw00422=true := by decide +kernel
#print axioms leaf00422_raw
theorem leaf00422_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00422=true := by decide +kernel
#print axioms leaf00422_rectangular
def affine00422 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00422 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)]))
theorem leaf00422_transform : affine00422=(NestedInteger.clearedAll 3 raw00422 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(3/4)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00422_transform
theorem leaf00422_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00422=true := by decide +kernel
#print axioms leaf00422_sign
theorem leaf00422_log : RationalLog.accepts (40100209/33554432) (382708623/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00422_log
def leaf00422 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1968305149/62500000000) (40100209/33554432) (382708623/4294967296) 0 8 ![52,0,4] ![(7/16),0,(3/4)] ![(1/16),1,(1/4)] affine00422
theorem leaf00422_checked : FastNestedCellData.accepts 1 0 4 leaf00422=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1968305149/62500000000) (40100209/33554432) (382708623/4294967296) 0 8 ![52,0,4] ![(7/16),0,(3/4)] ![(1/16),1,(1/4)] 138507161493559821991936000000000000 170739973317662440273242751277989888 5421541643466941170450432000000000000 raw00422 affine00422
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00422_raw leaf00422_rectangular
    leaf00422_transform leaf00422_sign leaf00422_log
#print axioms leaf00422_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
