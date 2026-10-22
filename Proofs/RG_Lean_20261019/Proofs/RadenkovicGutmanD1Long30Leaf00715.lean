/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00715 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 645514129909896572052137805086720000000000 22009468425153811995222684187060221247488 25158428757794974758869139456000000000000))
theorem leaf00715_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 645514129909896572052137805086720000000000 22009468425153811995222684187060221247488 25158428757794974758869139456000000000000 raw00715=true := by decide +kernel
#print axioms leaf00715_raw
theorem leaf00715_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00715=true := by decide +kernel
#print axioms leaf00715_rectangular
def affine00715 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00715 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00715_transform : affine00715=(NestedInteger.clearedAll 3 raw00715 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00715_transform
theorem leaf00715_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00715=true := by decide +kernel
#print axioms leaf00715_sign
theorem leaf00715_log : RationalLog.accepts (78108925/4294967296) (-8605170971/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00715_log
def leaf00715 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (874834777523/1000000000000) (78108925/4294967296) (-8605170971/4294967296) 6 8 ![60,0,4] ![(97/3200),0,0] ![(3/6400),1,(1/16)] affine00715
theorem leaf00715_checked : FastNestedCellData.accepts 1 2 4 leaf00715=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (874834777523/1000000000000) (78108925/4294967296) (-8605170971/4294967296) 6 8 ![60,0,4] ![(97/3200),0,0] ![(3/6400),1,(1/16)] 645514129909896572052137805086720000000000 22009468425153811995222684187060221247488 25158428757794974758869139456000000000000 raw00715 affine00715
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00715_raw leaf00715_rectangular
    leaf00715_transform leaf00715_sign leaf00715_log
#print axioms leaf00715_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
