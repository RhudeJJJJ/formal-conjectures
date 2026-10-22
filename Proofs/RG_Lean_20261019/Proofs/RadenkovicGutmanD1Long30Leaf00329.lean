/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00329 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18778371397583787005210263552000000000000 17573443223286143031399943040208671342592 616539107622233215463652851712000000000000))
theorem leaf00329_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18778371397583787005210263552000000000000 17573443223286143031399943040208671342592 616539107622233215463652851712000000000000 raw00329=true := by decide +kernel
#print axioms leaf00329_raw
theorem leaf00329_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00329=true := by decide +kernel
#print axioms leaf00329_rectangular
def affine00329 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00329 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00329_transform : affine00329=(NestedInteger.clearedAll 3 raw00329 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00329_transform
theorem leaf00329_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00329=true := by decide +kernel
#print axioms leaf00329_sign
theorem leaf00329_log : RationalLog.accepts (1953993363/2147483648) (-202768885/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00329_log
def leaf00329 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (28503371491/1000000000000) (1953993363/2147483648) (-202768885/4294967296) 1 8 ![60,0,4] ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00329
theorem leaf00329_checked : FastNestedCellData.accepts 1 2 4 leaf00329=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (28503371491/1000000000000) (1953993363/2147483648) (-202768885/4294967296) 1 8 ![60,0,4] ![(49/6400),0,(1/2)] ![(1/6400),1,(1/2)] 18778371397583787005210263552000000000000 17573443223286143031399943040208671342592 616539107622233215463652851712000000000000 raw00329 affine00329
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00329_raw leaf00329_rectangular
    leaf00329_transform leaf00329_sign leaf00329_log
#print axioms leaf00329_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
