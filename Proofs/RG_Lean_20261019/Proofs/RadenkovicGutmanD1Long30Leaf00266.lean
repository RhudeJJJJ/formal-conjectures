/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00266 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12997850282335983048889204736000000000000 8669822074227481842097167954355194691584 48063834082990676309006352384000000000000))
theorem leaf00266_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12997850282335983048889204736000000000000 8669822074227481842097167954355194691584 48063834082990676309006352384000000000000 raw00266=true := by decide +kernel
#print axioms leaf00266_raw
theorem leaf00266_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00266=true := by decide +kernel
#print axioms leaf00266_rectangular
def affine00266 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00266 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00266_transform : affine00266=(NestedInteger.clearedAll 3 raw00266 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00266_transform
theorem leaf00266_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00266=true := by decide +kernel
#print axioms leaf00266_sign
theorem leaf00266_log : RationalLog.accepts (2427035649/4294967296) (-306431605/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00266_log
def leaf00266 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11273838011/62500000000) (2427035649/4294967296) (-306431605/1073741824) 1 8 ![60,0,4] ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00266
theorem leaf00266_checked : FastNestedCellData.accepts 1 2 4 leaf00266=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11273838011/62500000000) (2427035649/4294967296) (-306431605/1073741824) 1 8 ![60,0,4] ![(37/6400),0,(1/16)] ![(1/6400),1,(1/16)] 12997850282335983048889204736000000000000 8669822074227481842097167954355194691584 48063834082990676309006352384000000000000 raw00266 affine00266
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00266_raw leaf00266_rectangular
    leaf00266_transform leaf00266_sign leaf00266_log
#print axioms leaf00266_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
