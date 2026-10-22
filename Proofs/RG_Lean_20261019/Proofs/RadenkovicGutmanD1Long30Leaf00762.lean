/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00762 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 125917752661704566998864756736000000000000 53320113823704593708258257992032729432064 122051705490233730372212883456000000000000))
theorem leaf00762_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 125917752661704566998864756736000000000000 53320113823704593708258257992032729432064 122051705490233730372212883456000000000000 raw00762=true := by decide +kernel
#print axioms leaf00762_raw
theorem leaf00762_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00762=true := by decide +kernel
#print axioms leaf00762_rectangular
def affine00762 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00762 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00762_transform : affine00762=(NestedInteger.clearedAll 3 raw00762 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00762_transform
theorem leaf00762_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00762=true := by decide +kernel
#print axioms leaf00762_sign
theorem leaf00762_log : RationalLog.accepts (158218777/536870912) (-2623750363/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00762_log
def leaf00762 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (436864963169/1000000000000) (158218777/536870912) (-2623750363/4294967296) 2 8 ![60,0,4] ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)] affine00762
theorem leaf00762_checked : FastNestedCellData.accepts 1 2 4 leaf00762=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (436864963169/1000000000000) (158218777/536870912) (-2623750363/4294967296) 2 8 ![60,0,4] ![(7/200),0,(1/8)] ![(3/3200),1,(1/8)] 125917752661704566998864756736000000000000 53320113823704593708258257992032729432064 122051705490233730372212883456000000000000 raw00762 affine00762
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00762_raw leaf00762_rectangular
    leaf00762_transform leaf00762_sign leaf00762_log
#print axioms leaf00762_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
