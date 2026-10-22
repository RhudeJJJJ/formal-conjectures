/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00351 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 294613037648677634179432710144000000000000 167697018928342854595464524158227141623808 656255747960160754750594220032000000000000))
theorem leaf00351_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 294613037648677634179432710144000000000000 167697018928342854595464524158227141623808 656255747960160754750594220032000000000000 raw00351=true := by decide +kernel
#print axioms leaf00351_raw
theorem leaf00351_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00351=true := by decide +kernel
#print axioms leaf00351_rectangular
def affine00351 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00351 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00351_transform : affine00351=(NestedInteger.clearedAll 3 raw00351 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00351_transform
theorem leaf00351_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00351=true := by decide +kernel
#print axioms leaf00351_sign
theorem leaf00351_log : RationalLog.accepts (486792697/1073741824) (-424700611/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00351_log
def leaf00351 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (255536076369/1000000000000) (486792697/1073741824) (-424700611/1073741824) 2 8 ![60,0,4] ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00351
theorem leaf00351_checked : FastNestedCellData.accepts 1 2 4 leaf00351=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (255536076369/1000000000000) (486792697/1073741824) (-424700611/1073741824) 2 8 ![60,0,4] ![(27/3200),0,(1/16)] ![(1/6400),1,(1/16)] 294613037648677634179432710144000000000000 167697018928342854595464524158227141623808 656255747960160754750594220032000000000000 raw00351 affine00351
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00351_raw leaf00351_rectangular
    leaf00351_transform leaf00351_sign leaf00351_log
#print axioms leaf00351_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
