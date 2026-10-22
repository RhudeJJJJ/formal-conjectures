/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00556 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8312368825898559515079928184832000000000000 3143196600904092128697810085968917343240192 6975357384236832681132919095296000000000000))
theorem leaf00556_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8312368825898559515079928184832000000000000 3143196600904092128697810085968917343240192 6975357384236832681132919095296000000000000 raw00556=true := by decide +kernel
#print axioms leaf00556_raw
theorem leaf00556_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00556=true := by decide +kernel
#print axioms leaf00556_rectangular
def affine00556 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00556 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00556_transform : affine00556=(NestedInteger.clearedAll 3 raw00556 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00556_transform
theorem leaf00556_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00556=true := by decide +kernel
#print axioms leaf00556_sign
theorem leaf00556_log : RationalLog.accepts (1119578663/4294967296) (-2887273625/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00556_log
def leaf00556 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (450614416977/1000000000000) (1119578663/4294967296) (-2887273625/4294967296) 2 8 ![60,0,4] ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)] affine00556
theorem leaf00556_checked : FastNestedCellData.accepts 1 2 4 leaf00556=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (450614416977/1000000000000) (1119578663/4294967296) (-2887273625/4294967296) 2 8 ![60,0,4] ![(27/1600),0,(1/16)] ![(1/3200),1,(1/16)] 8312368825898559515079928184832000000000000 3143196600904092128697810085968917343240192 6975357384236832681132919095296000000000000 raw00556 affine00556
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00556_raw leaf00556_rectangular
    leaf00556_transform leaf00556_sign leaf00556_log
#print axioms leaf00556_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
