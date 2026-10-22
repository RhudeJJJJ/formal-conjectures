/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00843 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5944152542478108579374995341312000000000000 3283173118970810254966582932182382334181376 10188812255832236037833404448768000000000000))
theorem leaf00843_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5944152542478108579374995341312000000000000 3283173118970810254966582932182382334181376 10188812255832236037833404448768000000000000 raw00843=true := by decide +kernel
#print axioms leaf00843_raw
theorem leaf00843_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00843=true := by decide +kernel
#print axioms leaf00843_rectangular
def affine00843 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00843 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00843_transform : affine00843=(NestedInteger.clearedAll 3 raw00843 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00843_transform
theorem leaf00843_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00843=true := by decide +kernel
#print axioms leaf00843_sign
theorem leaf00843_log : RationalLog.accepts (1794137219/4294967296) (-1874580837/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00843_log
def leaf00843 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (322233155007/1000000000000) (1794137219/4294967296) (-1874580837/4294967296) 2 8 ![60,0,4] ![(1/20),0,(1/4)] ![(1/640),1,(1/4)] affine00843
theorem leaf00843_checked : FastNestedCellData.accepts 1 2 4 leaf00843=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (322233155007/1000000000000) (1794137219/4294967296) (-1874580837/4294967296) 2 8 ![60,0,4] ![(1/20),0,(1/4)] ![(1/640),1,(1/4)] 5944152542478108579374995341312000000000000 3283173118970810254966582932182382334181376 10188812255832236037833404448768000000000000 raw00843 affine00843
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00843_raw leaf00843_rectangular
    leaf00843_transform leaf00843_sign leaf00843_log
#print axioms leaf00843_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
