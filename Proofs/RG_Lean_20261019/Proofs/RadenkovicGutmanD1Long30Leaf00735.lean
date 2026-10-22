/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00735 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4046585971924583608045250019328000000000000 155450766801660841867909056931425224228864 177159248014710503302655639552000000000000))
theorem leaf00735_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4046585971924583608045250019328000000000000 155450766801660841867909056931425224228864 177159248014710503302655639552000000000000 raw00735=true := by decide +kernel
#print axioms leaf00735_raw
theorem leaf00735_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00735=true := by decide +kernel
#print axioms leaf00735_rectangular
def affine00735 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00735 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00735_transform : affine00735=(NestedInteger.clearedAll 3 raw00735 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00735_transform
theorem leaf00735_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00735=true := by decide +kernel
#print axioms leaf00735_sign
theorem leaf00735_log : RationalLog.accepts (87880489/4294967296) (-8352039589/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00735_log
def leaf00735 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (438731730191/500000000000) (87880489/4294967296) (-8352039589/4294967296) 6 8 ![60,0,4] ![(103/3200),0,0] ![(3/6400),1,(1/16)] affine00735
theorem leaf00735_checked : FastNestedCellData.accepts 1 2 4 leaf00735=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (438731730191/500000000000) (87880489/4294967296) (-8352039589/4294967296) 6 8 ![60,0,4] ![(103/3200),0,0] ![(3/6400),1,(1/16)] 4046585971924583608045250019328000000000000 155450766801660841867909056931425224228864 177159248014710503302655639552000000000000 raw00735 affine00735
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00735_raw leaf00735_rectangular
    leaf00735_transform leaf00735_sign leaf00735_log
#print axioms leaf00735_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
