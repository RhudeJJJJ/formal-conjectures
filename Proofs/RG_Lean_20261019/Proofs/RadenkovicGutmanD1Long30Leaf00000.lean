/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00000 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 28233333651878711902452318208000000000000 204024136414980105811799814122242048 2082855475304623834660864000000000000))
theorem leaf00000_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 28233333651878711902452318208000000000000 204024136414980105811799814122242048 2082855475304623834660864000000000000 raw00000=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00000=true := by decide +kernel
#print axioms leaf00000_rectangular
def affine00000 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00000_transform : affine00000=(NestedInteger.clearedAll 3 raw00000 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/1000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00000_transform
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00000=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (7067/1073741824) (-25622109239/4294967296) 18 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)] affine00000
theorem leaf00000_checked : FastNestedCellData.accepts 1 2 4 leaf00000=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)] 28233333651878711902452318208000000000000 204024136414980105811799814122242048 2082855475304623834660864000000000000 raw00000 affine00000
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00000_raw leaf00000_rectangular
    leaf00000_transform leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
