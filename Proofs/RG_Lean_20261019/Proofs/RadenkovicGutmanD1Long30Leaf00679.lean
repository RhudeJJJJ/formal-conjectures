/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00679 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1784504284421978871859179945984000000000000 1448842582590502553673815114072019028672512 14976948252492645087088149004288000000000000))
theorem leaf00679_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1784504284421978871859179945984000000000000 1448842582590502553673815114072019028672512 14976948252492645087088149004288000000000000 raw00679=true := by decide +kernel
#print axioms leaf00679_raw
theorem leaf00679_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00679=true := by decide +kernel
#print axioms leaf00679_rectangular
def affine00679 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00679 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00679_transform : affine00679=(NestedInteger.clearedAll 3 raw00679 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00679_transform
theorem leaf00679_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00679=true := by decide +kernel
#print axioms leaf00679_sign
theorem leaf00679_log : RationalLog.accepts (3179512297/4294967296) (-322891495/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00679_log
def leaf00679 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (96738171099/1000000000000) (3179512297/4294967296) (-322891495/2147483648) 1 8 ![60,0,4] ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)] affine00679
theorem leaf00679_checked : FastNestedCellData.accepts 1 2 4 leaf00679=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (96738171099/1000000000000) (3179512297/4294967296) (-322891495/2147483648) 1 8 ![60,0,4] ![(17/640),0,(1/2)] ![(3/6400),1,(1/2)] 1784504284421978871859179945984000000000000 1448842582590502553673815114072019028672512 14976948252492645087088149004288000000000000 raw00679 affine00679
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00679_raw leaf00679_rectangular
    leaf00679_transform leaf00679_sign leaf00679_log
#print axioms leaf00679_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
