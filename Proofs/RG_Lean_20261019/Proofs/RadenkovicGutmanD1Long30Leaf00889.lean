/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00889 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 52070810109684405621526573875200000000000 35617239293898064550655090552857545408512 168238109216437340125195455692800000000000))
theorem leaf00889_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 52070810109684405621526573875200000000000 35617239293898064550655090552857545408512 168238109216437340125195455692800000000000 raw00889=true := by decide +kernel
#print axioms leaf00889_raw
theorem leaf00889_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00889=true := by decide +kernel
#print axioms leaf00889_rectangular
def affine00889 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00889 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00889_transform : affine00889=(NestedInteger.clearedAll 3 raw00889 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00889_transform
theorem leaf00889_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00889=true := by decide +kernel
#print axioms leaf00889_sign
theorem leaf00889_log : RationalLog.accepts (2424532719/4294967296) (-1227942199/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00889_log
def leaf00889 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42341464083/200000000000) (2424532719/4294967296) (-1227942199/4294967296) 1 8 ![60,0,4] ![(41/640),0,(1/2)] ![(1/640),1,(1/2)] affine00889
theorem leaf00889_checked : FastNestedCellData.accepts 1 2 4 leaf00889=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42341464083/200000000000) (2424532719/4294967296) (-1227942199/4294967296) 1 8 ![60,0,4] ![(41/640),0,(1/2)] ![(1/640),1,(1/2)] 52070810109684405621526573875200000000000 35617239293898064550655090552857545408512 168238109216437340125195455692800000000000 raw00889 affine00889
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00889_raw leaf00889_rectangular
    leaf00889_transform leaf00889_sign leaf00889_log
#print axioms leaf00889_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
