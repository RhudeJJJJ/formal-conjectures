/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00010 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 404619117822202282226323397017600000000000 4099524397637612669114583198908547072 37379784620250965427093504000000000000))
theorem leaf00010_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 404619117822202282226323397017600000000000 4099524397637612669114583198908547072 37379784620250965427093504000000000000 raw00010=true := by decide +kernel
#print axioms leaf00010_raw
theorem leaf00010_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00010=true := by decide +kernel
#print axioms leaf00010_rectangular
def affine00010 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00010 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/8000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00010_transform : affine00010=(NestedInteger.clearedAll 3 raw00010 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/8000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00010_transform
theorem leaf00010_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00010=true := by decide +kernel
#print axioms leaf00010_sign
theorem leaf00010_log : RationalLog.accepts (39215/4294967296) (-24919175735/4294967296) 17 8=true := by decide +kernel
#print axioms leaf00010_log
def leaf00010 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (109672231643/1000000000000) (39215/4294967296) (-24919175735/4294967296) 17 8 ![60,0,4] ![(9/8000),0,0] ![(1/16000),1,(1/16)] affine00010
theorem leaf00010_checked : FastNestedCellData.accepts 1 2 4 leaf00010=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (109672231643/1000000000000) (39215/4294967296) (-24919175735/4294967296) 17 8 ![60,0,4] ![(9/8000),0,0] ![(1/16000),1,(1/16)] 404619117822202282226323397017600000000000 4099524397637612669114583198908547072 37379784620250965427093504000000000000 raw00010 affine00010
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00010_raw leaf00010_rectangular
    leaf00010_transform leaf00010_sign leaf00010_log
#print axioms leaf00010_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
