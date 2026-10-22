/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00845 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1006629362965597324848473833472000000000000 95885959743057994799098498090864365010944 109820942091290968858350845952000000000000))
theorem leaf00845_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1006629362965597324848473833472000000000000 95885959743057994799098498090864365010944 109820942091290968858350845952000000000000 raw00845=true := by decide +kernel
#print axioms leaf00845_raw
theorem leaf00845_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00845=true := by decide +kernel
#print axioms leaf00845_rectangular
def affine00845 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00845 (IntegerComputedClassCell.leftNumerator ![(33/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/640),0,0] ![(1/640),1,(1/16)]))
theorem leaf00845_transform : affine00845=(NestedInteger.clearedAll 3 raw00845 (IntegerComputedClassCell.leftNumerator ![(33/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/640),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00845_transform
theorem leaf00845_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00845=true := by decide +kernel
#print axioms leaf00845_sign
theorem leaf00845_log : RationalLog.accepts (218414561/4294967296) (-6396933717/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00845_log
def leaf00845 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (218277948443/250000000000) (218414561/4294967296) (-6396933717/4294967296) 5 8 ![60,0,4] ![(33/640),0,0] ![(1/640),1,(1/16)] affine00845
theorem leaf00845_checked : FastNestedCellData.accepts 1 2 4 leaf00845=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (218277948443/250000000000) (218414561/4294967296) (-6396933717/4294967296) 5 8 ![60,0,4] ![(33/640),0,0] ![(1/640),1,(1/16)] 1006629362965597324848473833472000000000000 95885959743057994799098498090864365010944 109820942091290968858350845952000000000000 raw00845 affine00845
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00845_raw leaf00845_rectangular
    leaf00845_transform leaf00845_sign leaf00845_log
#print axioms leaf00845_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
