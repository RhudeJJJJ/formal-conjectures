/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00240 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 396957689555592664508521041100800000000000 241787361571423252713456413639247396864 561796596528820368403595264000000000000))
theorem leaf00240_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 396957689555592664508521041100800000000000 241787361571423252713456413639247396864 561796596528820368403595264000000000000 raw00240=true := by decide +kernel
#print axioms leaf00240_raw
theorem leaf00240_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00240=true := by decide +kernel
#print axioms leaf00240_rectangular
def affine00240 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00240 (IntegerComputedClassCell.leftNumerator ![(1/200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00240_transform : affine00240=(NestedInteger.clearedAll 3 raw00240 (IntegerComputedClassCell.leftNumerator ![(1/200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00240_transform
theorem leaf00240_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00240=true := by decide +kernel
#print axioms leaf00240_sign
theorem leaf00240_log : RationalLog.accepts (914465/2147483648) (-16667626303/4294967296) 12 8=true := by decide +kernel
#print axioms leaf00240_log
def leaf00240 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (430382389401/1000000000000) (914465/2147483648) (-16667626303/4294967296) 12 8 ![60,0,4] ![(1/200),0,0] ![(1/6400),1,(1/16)] affine00240
theorem leaf00240_checked : FastNestedCellData.accepts 1 2 4 leaf00240=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (430382389401/1000000000000) (914465/2147483648) (-16667626303/4294967296) 12 8 ![60,0,4] ![(1/200),0,0] ![(1/6400),1,(1/16)] 396957689555592664508521041100800000000000 241787361571423252713456413639247396864 561796596528820368403595264000000000000 raw00240 affine00240
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00240_raw leaf00240_rectangular
    leaf00240_transform leaf00240_sign leaf00240_log
#print axioms leaf00240_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
