/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00871 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 698848406958555696125811097600000000000 186549353952435424383157208668698574848 256465684237001195793049190400000000000))
theorem leaf00871_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 698848406958555696125811097600000000000 186549353952435424383157208668698574848 256465684237001195793049190400000000000 raw00871=true := by decide +kernel
#print axioms leaf00871_raw
theorem leaf00871_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00871=true := by decide +kernel
#print axioms leaf00871_rectangular
def affine00871 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00871 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00871_transform : affine00871=(NestedInteger.clearedAll 3 raw00871 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00871_transform
theorem leaf00871_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00871=true := by decide +kernel
#print axioms leaf00871_sign
theorem leaf00871_log : RationalLog.accepts (165928671/1073741824) (-250631059/268435456) 3 8=true := by decide +kernel
#print axioms leaf00871_log
def leaf00871 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36369262131/50000000000) (165928671/1073741824) (-250631059/268435456) 3 8 ![60,0,4] ![(19/320),0,(1/16)] ![(1/640),1,(1/16)] affine00871
theorem leaf00871_checked : FastNestedCellData.accepts 1 2 4 leaf00871=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36369262131/50000000000) (165928671/1073741824) (-250631059/268435456) 3 8 ![60,0,4] ![(19/320),0,(1/16)] ![(1/640),1,(1/16)] 698848406958555696125811097600000000000 186549353952435424383157208668698574848 256465684237001195793049190400000000000 raw00871 affine00871
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00871_raw leaf00871_rectangular
    leaf00871_transform leaf00871_sign leaf00871_log
#print axioms leaf00871_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
