/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00775 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 162527130841324635651096497356800000000000 8567568642520227249735591438361357713408 9724145455862875121830697369600000000000))
theorem leaf00775_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 162527130841324635651096497356800000000000 8567568642520227249735591438361357713408 9724145455862875121830697369600000000000 raw00775=true := by decide +kernel
#print axioms leaf00775_raw
theorem leaf00775_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00775=true := by decide +kernel
#print axioms leaf00775_rectangular
def affine00775 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00775 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00775_transform : affine00775=(NestedInteger.clearedAll 3 raw00775 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00775_transform
theorem leaf00775_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00775=true := by decide +kernel
#print axioms leaf00775_sign
theorem leaf00775_log : RationalLog.accepts (120361787/4294967296) (-3838301913/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00775_log
def leaf00775 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (88106134173/100000000000) (120361787/4294967296) (-3838301913/2147483648) 6 8 ![60,0,4] ![(121/3200),0,0] ![(3/3200),1,(1/16)] affine00775
theorem leaf00775_checked : FastNestedCellData.accepts 1 2 4 leaf00775=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (88106134173/100000000000) (120361787/4294967296) (-3838301913/2147483648) 6 8 ![60,0,4] ![(121/3200),0,0] ![(3/3200),1,(1/16)] 162527130841324635651096497356800000000000 8567568642520227249735591438361357713408 9724145455862875121830697369600000000000 raw00775 affine00775
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00775_raw leaf00775_rectangular
    leaf00775_transform leaf00775_sign leaf00775_log
#print axioms leaf00775_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
