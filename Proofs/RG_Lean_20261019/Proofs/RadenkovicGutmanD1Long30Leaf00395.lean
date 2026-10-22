/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00395 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12257816447566363816007045218304000000000000 38345024027171935214576140576914665373696 57705289335599240496896016384000000000000))
theorem leaf00395_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12257816447566363816007045218304000000000000 38345024027171935214576140576914665373696 57705289335599240496896016384000000000000 raw00395=true := by decide +kernel
#print axioms leaf00395_raw
theorem leaf00395_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00395=true := by decide +kernel
#print axioms leaf00395_rectangular
def affine00395 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00395 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00395_transform : affine00395=(NestedInteger.clearedAll 3 raw00395 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00395_transform
theorem leaf00395_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00395=true := by decide +kernel
#print axioms leaf00395_sign
theorem leaf00395_log : RationalLog.accepts (8071841/4294967296) (-6739681793/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00395_log
def leaf00395 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (664497561119/1000000000000) (8071841/4294967296) (-6739681793/2147483648) 10 8 ![60,0,4] ![(63/6400),0,0] ![(1/6400),1,(1/16)] affine00395
theorem leaf00395_checked : FastNestedCellData.accepts 1 2 4 leaf00395=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (664497561119/1000000000000) (8071841/4294967296) (-6739681793/2147483648) 10 8 ![60,0,4] ![(63/6400),0,0] ![(1/6400),1,(1/16)] 12257816447566363816007045218304000000000000 38345024027171935214576140576914665373696 57705289335599240496896016384000000000000 raw00395 affine00395
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00395_raw leaf00395_rectangular
    leaf00395_transform leaf00395_sign leaf00395_log
#print axioms leaf00395_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
