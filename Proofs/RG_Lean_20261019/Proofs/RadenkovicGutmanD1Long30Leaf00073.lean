/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00073 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 267837052820406933536565624832000000000000 258775028123539221388827227032394865311744 17822615154232367510663852982272000000000000))
theorem leaf00073_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 267837052820406933536565624832000000000000 258775028123539221388827227032394865311744 17822615154232367510663852982272000000000000 raw00073=true := by decide +kernel
#print axioms leaf00073_raw
theorem leaf00073_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00073=true := by decide +kernel
#print axioms leaf00073_rectangular
def affine00073 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00073 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00073_transform : affine00073=(NestedInteger.clearedAll 3 raw00073 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00073_transform
theorem leaf00073_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00073=true := by decide +kernel
#print axioms leaf00073_sign
theorem leaf00073_log : RationalLog.accepts (4090262491/4294967296) (-104871959/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00073_log
def leaf00073 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14519475727/1000000000000) (4090262491/4294967296) (-104871959/4294967296) 1 8 ![60,0,4] ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)] affine00073
theorem leaf00073_checked : FastNestedCellData.accepts 1 2 4 leaf00073=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14519475727/1000000000000) (4090262491/4294967296) (-104871959/4294967296) 1 8 ![60,0,4] ![(3/1600),0,(1/4)] ![(1/16000),1,(1/4)] 267837052820406933536565624832000000000000 258775028123539221388827227032394865311744 17822615154232367510663852982272000000000000 raw00073 affine00073
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00073_raw leaf00073_rectangular
    leaf00073_transform leaf00073_sign leaf00073_log
#print axioms leaf00073_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
