/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00766 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12258152907914126933206641934336000000000000 3129104221903495458367305521337054814797824 4708848485986124218973598777344000000000000))
theorem leaf00766_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12258152907914126933206641934336000000000000 3129104221903495458367305521337054814797824 4708848485986124218973598777344000000000000 raw00766=true := by decide +kernel
#print axioms leaf00766_raw
theorem leaf00766_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00766=true := by decide +kernel
#print axioms leaf00766_rectangular
def affine00766 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00766 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00766_transform : affine00766=(NestedInteger.clearedAll 3 raw00766 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00766_transform
theorem leaf00766_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00766=true := by decide +kernel
#print axioms leaf00766_sign
theorem leaf00766_log : RationalLog.accepts (658668559/4294967296) (-503310791/536870912) 3 8=true := by decide +kernel
#print axioms leaf00766_log
def leaf00766 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (664515800671/1000000000000) (658668559/4294967296) (-503310791/536870912) 3 8 ![60,0,4] ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)] affine00766
theorem leaf00766_checked : FastNestedCellData.accepts 1 2 4 leaf00766=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (664515800671/1000000000000) (658668559/4294967296) (-503310791/536870912) 3 8 ![60,0,4] ![(23/640),0,(1/16)] ![(3/3200),1,(1/16)] 12258152907914126933206641934336000000000000 3129104221903495458367305521337054814797824 4708848485986124218973598777344000000000000 raw00766 affine00766
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00766_raw leaf00766_rectangular
    leaf00766_transform leaf00766_sign leaf00766_log
#print axioms leaf00766_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
