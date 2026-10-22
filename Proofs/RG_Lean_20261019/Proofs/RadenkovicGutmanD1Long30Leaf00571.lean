/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00571 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33692241126479354204287664128000000000000 12309065338605275047777144018496670138368 26325397287343683370867490816000000000000))
theorem leaf00571_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33692241126479354204287664128000000000000 12309065338605275047777144018496670138368 26325397287343683370867490816000000000000 raw00571=true := by decide +kernel
#print axioms leaf00571_raw
theorem leaf00571_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00571=true := by decide +kernel
#print axioms leaf00571_rectangular
def affine00571 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00571 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00571_transform : affine00571=(NestedInteger.clearedAll 3 raw00571 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00571_transform
theorem leaf00571_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00571=true := by decide +kernel
#print axioms leaf00571_sign
theorem leaf00571_log : RationalLog.accepts (66824407/268435456) (-2986166551/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00571_log
def leaf00571 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (467573773123/1000000000000) (66824407/268435456) (-2986166551/4294967296) 3 8 ![60,0,4] ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00571
theorem leaf00571_checked : FastNestedCellData.accepts 1 2 4 leaf00571=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (467573773123/1000000000000) (66824407/268435456) (-2986166551/4294967296) 3 8 ![60,0,4] ![(57/3200),0,(1/16)] ![(1/3200),1,(1/16)] 33692241126479354204287664128000000000000 12309065338605275047777144018496670138368 26325397287343683370867490816000000000000 raw00571 affine00571
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00571_raw leaf00571_rectangular
    leaf00571_transform leaf00571_sign leaf00571_log
#print axioms leaf00571_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
