/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00149 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 43566677690485372691446497280000000000 37087501975326774990916836604319367168 523445665004550169716661944320000000000))
theorem leaf00149_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 43566677690485372691446497280000000000 37087501975326774990916836604319367168 523445665004550169716661944320000000000 raw00149=true := by decide +kernel
#print axioms leaf00149_raw
theorem leaf00149_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00149=true := by decide +kernel
#print axioms leaf00149_rectangular
def affine00149 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00149 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00149_transform : affine00149=(NestedInteger.clearedAll 3 raw00149 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00149_transform
theorem leaf00149_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00149=true := by decide +kernel
#print axioms leaf00149_sign
theorem leaf00149_log : RationalLog.accepts (3414312699/4294967296) (-492778229/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00149_log
def leaf00149 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (708526299/10000000000) (3414312699/4294967296) (-492778229/4294967296) 1 8 ![52,0,4] ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00149
theorem leaf00149_checked : FastNestedCellData.accepts 1 0 4 leaf00149=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (708526299/10000000000) (3414312699/4294967296) (-492778229/4294967296) 1 8 ![52,0,4] ![(31/1600),0,(1/2)] ![(1/1600),1,(1/2)] 43566677690485372691446497280000000000 37087501975326774990916836604319367168 523445665004550169716661944320000000000 raw00149 affine00149
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00149_raw leaf00149_rectangular
    leaf00149_transform leaf00149_sign leaf00149_log
#print axioms leaf00149_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
