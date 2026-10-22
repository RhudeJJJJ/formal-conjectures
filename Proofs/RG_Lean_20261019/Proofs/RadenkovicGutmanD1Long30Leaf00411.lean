/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00411 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1405691428856066319007621316608000000000000 721832421666785605351131095426574269284352 2368133160886728291962455064576000000000000))
theorem leaf00411_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1405691428856066319007621316608000000000000 721832421666785605351131095426574269284352 2368133160886728291962455064576000000000000 raw00411=true := by decide +kernel
#print axioms leaf00411_raw
theorem leaf00411_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00411=true := by decide +kernel
#print axioms leaf00411_rectangular
def affine00411 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00411 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00411_transform : affine00411=(NestedInteger.clearedAll 3 raw00411 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00411_transform
theorem leaf00411_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00411=true := by decide +kernel
#print axioms leaf00411_sign
theorem leaf00411_log : RationalLog.accepts (1690280287/4294967296) (-2002635035/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00411_log
def leaf00411 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (152405370101/500000000000) (1690280287/4294967296) (-2002635035/4294967296) 2 8 ![60,0,4] ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00411
theorem leaf00411_checked : FastNestedCellData.accepts 1 2 4 leaf00411=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (152405370101/500000000000) (1690280287/4294967296) (-2002635035/4294967296) 2 8 ![60,0,4] ![(33/3200),0,(1/16)] ![(1/6400),1,(1/16)] 1405691428856066319007621316608000000000000 721832421666785605351131095426574269284352 2368133160886728291962455064576000000000000 raw00411 affine00411
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00411_raw leaf00411_rectangular
    leaf00411_transform leaf00411_sign leaf00411_log
#print axioms leaf00411_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
