/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00669 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 26948490382408944694065102848000000000000 22012627350340899260565068240299361304576 235438340747199111406056112128000000000000))
theorem leaf00669_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 26948490382408944694065102848000000000000 22012627350340899260565068240299361304576 235438340747199111406056112128000000000000 raw00669=true := by decide +kernel
#print axioms leaf00669_raw
theorem leaf00669_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00669=true := by decide +kernel
#print axioms leaf00669_rectangular
def affine00669 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00669 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00669_transform : affine00669=(NestedInteger.clearedAll 3 raw00669 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00669_transform
theorem leaf00669_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00669=true := by decide +kernel
#print axioms leaf00669_sign
theorem leaf00669_log : RationalLog.accepts (401042107/536870912) (-626402229/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00669_log
def leaf00669 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93496357817/1000000000000) (401042107/536870912) (-626402229/4294967296) 1 8 ![60,0,4] ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)] affine00669
theorem leaf00669_checked : FastNestedCellData.accepts 1 2 4 leaf00669=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93496357817/1000000000000) (401042107/536870912) (-626402229/4294967296) 1 8 ![60,0,4] ![(41/1600),0,(1/2)] ![(3/6400),1,(1/2)] 26948490382408944694065102848000000000000 22012627350340899260565068240299361304576 235438340747199111406056112128000000000000 raw00669 affine00669
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00669_raw leaf00669_rectangular
    leaf00669_transform leaf00669_sign leaf00669_log
#print axioms leaf00669_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
