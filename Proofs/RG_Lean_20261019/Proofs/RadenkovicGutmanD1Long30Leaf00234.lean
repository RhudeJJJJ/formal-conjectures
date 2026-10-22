/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00234 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 258381485180288536886955212800000000000 247732268230123689503954355180225429504 13817546719158765261995114496000000000000))
theorem leaf00234_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 258381485180288536886955212800000000000 247732268230123689503954355180225429504 13817546719158765261995114496000000000000 raw00234=true := by decide +kernel
#print axioms leaf00234_raw
theorem leaf00234_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00234=true := by decide +kernel
#print axioms leaf00234_rectangular
def affine00234 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00234 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00234_transform : affine00234=(NestedInteger.clearedAll 3 raw00234 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00234_transform
theorem leaf00234_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00234=true := by decide +kernel
#print axioms leaf00234_sign
theorem leaf00234_log : RationalLog.accepts (1011355055/1073741824) (-128545207/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00234_log
def leaf00234 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4482204281/250000000000) (1011355055/1073741824) (-128545207/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00234
theorem leaf00234_checked : FastNestedCellData.accepts 1 2 4 leaf00234=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4482204281/250000000000) (1011355055/1073741824) (-128545207/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/2)] ![(3/32000),1,(1/2)] 258381485180288536886955212800000000000 247732268230123689503954355180225429504 13817546719158765261995114496000000000000 raw00234 affine00234
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00234_raw leaf00234_rectangular
    leaf00234_transform leaf00234_sign leaf00234_log
#print axioms leaf00234_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
