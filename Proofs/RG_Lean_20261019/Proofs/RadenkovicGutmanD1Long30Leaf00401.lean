/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00401 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5475626057426455026648580358144000000000000 2858924865255892936563544759841243988492288 9631383655904147042523238367232000000000000))
theorem leaf00401_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5475626057426455026648580358144000000000000 2858924865255892936563544759841243988492288 9631383655904147042523238367232000000000000 raw00401=true := by decide +kernel
#print axioms leaf00401_raw
theorem leaf00401_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00401=true := by decide +kernel
#print axioms leaf00401_rectangular
def affine00401 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00401 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00401_transform : affine00401=(NestedInteger.clearedAll 3 raw00401 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00401_transform
theorem leaf00401_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00401=true := by decide +kernel
#print axioms leaf00401_sign
theorem leaf00401_log : RationalLog.accepts (1729196463/4294967296) (-976876509/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00401_log
def leaf00401 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (296834283359/1000000000000) (1729196463/4294967296) (-976876509/2147483648) 2 8 ![60,0,4] ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)] affine00401
theorem leaf00401_checked : FastNestedCellData.accepts 1 2 4 leaf00401=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (296834283359/1000000000000) (1729196463/4294967296) (-976876509/2147483648) 2 8 ![60,0,4] ![(1/100),0,(1/16)] ![(1/6400),1,(1/16)] 5475626057426455026648580358144000000000000 2858924865255892936563544759841243988492288 9631383655904147042523238367232000000000000 raw00401 affine00401
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00401_raw leaf00401_rectangular
    leaf00401_transform leaf00401_sign leaf00401_log
#print axioms leaf00401_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
