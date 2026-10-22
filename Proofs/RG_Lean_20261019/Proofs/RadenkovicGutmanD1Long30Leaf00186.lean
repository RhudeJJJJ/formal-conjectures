/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00186 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 144339555146106556567479386112000000000000 108748577949336401598171317514464800014336 868636279128686865857986428928000000000000))
theorem leaf00186_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 144339555146106556567479386112000000000000 108748577949336401598171317514464800014336 868636279128686865857986428928000000000000 raw00186=true := by decide +kernel
#print axioms leaf00186_raw
theorem leaf00186_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00186=true := by decide +kernel
#print axioms leaf00186_rectangular
def affine00186 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00186 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00186_transform : affine00186=(NestedInteger.clearedAll 3 raw00186 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00186_transform
theorem leaf00186_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00186=true := by decide +kernel
#print axioms leaf00186_sign
theorem leaf00186_log : RationalLog.accepts (2875877899/4294967296) (-430662785/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00186_log
def leaf00186 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (31298651853/250000000000) (2875877899/4294967296) (-430662785/2147483648) 1 8 ![60,0,4] ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00186
theorem leaf00186_checked : FastNestedCellData.accepts 1 2 4 leaf00186=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (31298651853/250000000000) (2875877899/4294967296) (-430662785/2147483648) 1 8 ![60,0,4] ![(127/32000),0,(1/16)] ![(3/32000),1,(1/16)] 144339555146106556567479386112000000000000 108748577949336401598171317514464800014336 868636279128686865857986428928000000000000 raw00186 affine00186
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00186_raw leaf00186_rectangular
    leaf00186_transform leaf00186_sign leaf00186_log
#print axioms leaf00186_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
