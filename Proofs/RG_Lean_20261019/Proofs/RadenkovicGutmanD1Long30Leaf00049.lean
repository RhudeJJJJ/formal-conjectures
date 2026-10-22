/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00049 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 173669131881874579403743166464000000000 171214369899503858371076445688955928576 29097607654774872043422115430400000000000))
theorem leaf00049_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 173669131881874579403743166464000000000 171214369899503858371076445688955928576 29097607654774872043422115430400000000000 raw00049=true := by decide +kernel
#print axioms leaf00049_raw
theorem leaf00049_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00049=true := by decide +kernel
#print axioms leaf00049_rectangular
def affine00049 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00049 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00049_transform : affine00049=(NestedInteger.clearedAll 3 raw00049 (IntegerComputedClassCell.leftNumerator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00049_transform
theorem leaf00049_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00049=true := by decide +kernel
#print axioms leaf00049_sign
theorem leaf00049_log : RationalLog.accepts (4209489975/4294967296) (-43169713/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00049_log
def leaf00049 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1176827813/200000000000) (4209489975/4294967296) (-43169713/4294967296) 1 8 ![60,0,4] ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)] affine00049
theorem leaf00049_checked : FastNestedCellData.accepts 1 2 4 leaf00049=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1176827813/200000000000) (4209489975/4294967296) (-43169713/4294967296) 1 8 ![60,0,4] ![(1/640),0,(1/2)] ![(1/16000),1,(1/2)] 173669131881874579403743166464000000000 171214369899503858371076445688955928576 29097607654774872043422115430400000000000 raw00049 affine00049
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00049_raw leaf00049_rectangular
    leaf00049_transform leaf00049_sign leaf00049_log
#print axioms leaf00049_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
