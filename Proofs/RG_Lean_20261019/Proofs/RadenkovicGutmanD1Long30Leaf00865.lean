/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00865 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3990453282575251322785692123136000000000000 469490319181609278658004929120088239374336 542580450750085757946197704704000000000000))
theorem leaf00865_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3990453282575251322785692123136000000000000 469490319181609278658004929120088239374336 542580450750085757946197704704000000000000 raw00865=true := by decide +kernel
#print axioms leaf00865_raw
theorem leaf00865_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00865=true := by decide +kernel
#print axioms leaf00865_rectangular
def affine00865 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00865 (IntegerComputedClassCell.leftNumerator ![(37/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/640),0,0] ![(1/640),1,(1/16)]))
theorem leaf00865_transform : affine00865=(NestedInteger.clearedAll 3 raw00865 (IntegerComputedClassCell.leftNumerator ![(37/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/640),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00865_transform
theorem leaf00865_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00865=true := by decide +kernel
#print axioms leaf00865_sign
theorem leaf00865_log : RationalLog.accepts (270905319/4294967296) (-370901283/268435456) 4 8=true := by decide +kernel
#print axioms leaf00865_log
def leaf00865 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (432645811817/500000000000) (270905319/4294967296) (-370901283/268435456) 4 8 ![60,0,4] ![(37/640),0,0] ![(1/640),1,(1/16)] affine00865
theorem leaf00865_checked : FastNestedCellData.accepts 1 2 4 leaf00865=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (432645811817/500000000000) (270905319/4294967296) (-370901283/268435456) 4 8 ![60,0,4] ![(37/640),0,0] ![(1/640),1,(1/16)] 3990453282575251322785692123136000000000000 469490319181609278658004929120088239374336 542580450750085757946197704704000000000000 raw00865 affine00865
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00865_raw leaf00865_rectangular
    leaf00865_transform leaf00865_sign leaf00865_log
#print axioms leaf00865_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
