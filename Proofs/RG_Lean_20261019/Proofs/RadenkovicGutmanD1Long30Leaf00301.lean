/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00301 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 244445244123547789854439899136000000000000 152480022451976841479068245565817399279616 719169225558617045654260678656000000000000))
theorem leaf00301_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 244445244123547789854439899136000000000000 152480022451976841479068245565817399279616 719169225558617045654260678656000000000000 raw00301=true := by decide +kernel
#print axioms leaf00301_raw
theorem leaf00301_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00301=true := by decide +kernel
#print axioms leaf00301_rectangular
def affine00301 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00301 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00301_transform : affine00301=(NestedInteger.clearedAll 3 raw00301 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00301_transform
theorem leaf00301_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00301=true := by decide +kernel
#print axioms leaf00301_sign
theorem leaf00301_log : RationalLog.accepts (1105224633/2147483648) (-713231047/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00301_log
def leaf00301 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (106011225893/500000000000) (1105224633/2147483648) (-713231047/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)] affine00301
theorem leaf00301_checked : FastNestedCellData.accepts 1 2 4 leaf00301=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (106011225893/500000000000) (1105224633/2147483648) (-713231047/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/16)] ![(1/6400),1,(1/16)] 244445244123547789854439899136000000000000 152480022451976841479068245565817399279616 719169225558617045654260678656000000000000 raw00301 affine00301
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00301_raw leaf00301_rectangular
    leaf00301_transform leaf00301_sign leaf00301_log
#print axioms leaf00301_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
