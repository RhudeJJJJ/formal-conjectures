/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00476 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6232061533164516656807936000000000000 2887608367448304893336783753645654016 8151290444298300105424896000000000000))
theorem leaf00476_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6232061533164516656807936000000000000 2887608367448304893336783753645654016 8151290444298300105424896000000000000 raw00476=true := by decide +kernel
#print axioms leaf00476_raw
theorem leaf00476_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00476=true := by decide +kernel
#print axioms leaf00476_rectangular
def affine00476 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00476 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00476_transform : affine00476=(NestedInteger.clearedAll 3 raw00476 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00476_transform
theorem leaf00476_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00476=true := by decide +kernel
#print axioms leaf00476_sign
theorem leaf00476_log : RationalLog.accepts (367372839/1073741824) (-2303235589/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00476_log
def leaf00476 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1383795641/3906250000) (367372839/1073741824) (-2303235589/4294967296) 2 8 ![60,0,4] ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00476
theorem leaf00476_checked : FastNestedCellData.accepts 1 2 4 leaf00476=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1383795641/3906250000) (367372839/1073741824) (-2303235589/4294967296) 2 8 ![60,0,4] ![(79/6400),0,(1/16)] ![(1/6400),1,(1/16)] 6232061533164516656807936000000000000 2887608367448304893336783753645654016 8151290444298300105424896000000000000 raw00476 affine00476
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00476_raw leaf00476_rectangular
    leaf00476_transform leaf00476_sign leaf00476_log
#print axioms leaf00476_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
