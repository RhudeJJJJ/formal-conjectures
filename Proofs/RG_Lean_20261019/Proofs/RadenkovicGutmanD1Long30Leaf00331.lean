/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00331 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17177352512319601948519038976000000000000 10136039615212402376478049069092539727872 42519860218360356942739668992000000000000))
theorem leaf00331_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17177352512319601948519038976000000000000 10136039615212402376478049069092539727872 42519860218360356942739668992000000000000 raw00331=true := by decide +kernel
#print axioms leaf00331_raw
theorem leaf00331_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00331=true := by decide +kernel
#print axioms leaf00331_rectangular
def affine00331 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00331 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00331_transform : affine00331=(NestedInteger.clearedAll 3 raw00331 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00331_transform
theorem leaf00331_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00331=true := by decide +kernel
#print axioms leaf00331_sign
theorem leaf00331_log : RationalLog.accepts (255815429/536870912) (-795966433/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00331_log
def leaf00331 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (119191826633/500000000000) (255815429/536870912) (-795966433/2147483648) 2 8 ![60,0,4] ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)] affine00331
theorem leaf00331_checked : FastNestedCellData.accepts 1 2 4 leaf00331=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (119191826633/500000000000) (255815429/536870912) (-795966433/2147483648) 2 8 ![60,0,4] ![(1/128),0,(1/16)] ![(1/6400),1,(1/16)] 17177352512319601948519038976000000000000 10136039615212402376478049069092539727872 42519860218360356942739668992000000000000 raw00331 affine00331
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00331_raw leaf00331_rectangular
    leaf00331_transform leaf00331_sign leaf00331_log
#print axioms leaf00331_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
