/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00828 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 355441222398170689605166170112000000000000 199948904036828215117495478067140352802816 648561215638606988725052243968000000000000))
theorem leaf00828_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 355441222398170689605166170112000000000000 199948904036828215117495478067140352802816 648561215638606988725052243968000000000000 raw00828=true := by decide +kernel
#print axioms leaf00828_raw
theorem leaf00828_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00828=true := by decide +kernel
#print axioms leaf00828_rectangular
def affine00828 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00828 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00828_transform : affine00828=(NestedInteger.clearedAll 3 raw00828 (IntegerComputedClassCell.leftNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00828_transform
theorem leaf00828_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00828=true := by decide +kernel
#print axioms leaf00828_sign
theorem leaf00828_log : RationalLog.accepts (1846736969/4294967296) (-1812527079/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00828_log
def leaf00828 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77074029103/250000000000) (1846736969/4294967296) (-1812527079/4294967296) 2 8 ![60,0,4] ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00828
theorem leaf00828_checked : FastNestedCellData.accepts 1 2 4 leaf00828=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77074029103/250000000000) (1846736969/4294967296) (-1812527079/4294967296) 2 8 ![60,0,4] ![(151/3200),0,(1/4)] ![(3/3200),1,(1/4)] 355441222398170689605166170112000000000000 199948904036828215117495478067140352802816 648561215638606988725052243968000000000000 raw00828 affine00828
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00828_raw leaf00828_rectangular
    leaf00828_transform leaf00828_sign leaf00828_log
#print axioms leaf00828_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
