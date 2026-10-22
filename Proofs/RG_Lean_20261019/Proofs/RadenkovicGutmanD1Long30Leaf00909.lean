/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00909 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 55815763358294765897256638873600000000000 37680636370182706519350105327554732752896 166042712388936873027742518476800000000000))
theorem leaf00909_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 55815763358294765897256638873600000000000 37680636370182706519350105327554732752896 166042712388936873027742518476800000000000 raw00909=true := by decide +kernel
#print axioms leaf00909_raw
theorem leaf00909_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00909=true := by decide +kernel
#print axioms leaf00909_rectangular
def affine00909 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00909 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00909_transform : affine00909=(NestedInteger.clearedAll 3 raw00909 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00909_transform
theorem leaf00909_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00909=true := by decide +kernel
#print axioms leaf00909_sign
theorem leaf00909_log : RationalLog.accepts (2363198673/4294967296) (-1282966617/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00909_log
def leaf00909 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (45386678919/200000000000) (2363198673/4294967296) (-1282966617/4294967296) 1 8 ![60,0,4] ![(9/128),0,(1/2)] ![(1/640),1,(1/2)] affine00909
theorem leaf00909_checked : FastNestedCellData.accepts 1 2 4 leaf00909=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (45386678919/200000000000) (2363198673/4294967296) (-1282966617/4294967296) 1 8 ![60,0,4] ![(9/128),0,(1/2)] ![(1/640),1,(1/2)] 55815763358294765897256638873600000000000 37680636370182706519350105327554732752896 166042712388936873027742518476800000000000 raw00909 affine00909
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00909_raw leaf00909_rectangular
    leaf00909_transform leaf00909_sign leaf00909_log
#print axioms leaf00909_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
