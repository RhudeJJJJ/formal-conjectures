/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00720 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40378794909291065349075527270400000000000 1419486460808183711114550761617115578368 1621203871824764644482665676800000000000))
theorem leaf00720_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40378794909291065349075527270400000000000 1419486460808183711114550761617115578368 1621203871824764644482665676800000000000 raw00720=true := by decide +kernel
#print axioms leaf00720_raw
theorem leaf00720_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00720=true := by decide +kernel
#print axioms leaf00720_rectangular
def affine00720 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00720 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(197/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00720_transform : affine00720=(NestedInteger.clearedAll 3 raw00720 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(197/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00720_transform
theorem leaf00720_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00720=true := by decide +kernel
#print axioms leaf00720_sign
theorem leaf00720_log : RationalLog.accepts (80501357/4294967296) (-4270191001/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00720_log
def leaf00720 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43778777163/50000000000) (80501357/4294967296) (-4270191001/2147483648) 6 8 ![60,0,4] ![(197/6400),0,0] ![(3/6400),1,(1/16)] affine00720
theorem leaf00720_checked : FastNestedCellData.accepts 1 2 4 leaf00720=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43778777163/50000000000) (80501357/4294967296) (-4270191001/2147483648) 6 8 ![60,0,4] ![(197/6400),0,0] ![(3/6400),1,(1/16)] 40378794909291065349075527270400000000000 1419486460808183711114550761617115578368 1621203871824764644482665676800000000000 raw00720 affine00720
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00720_raw leaf00720_rectangular
    leaf00720_transform leaf00720_sign leaf00720_log
#print axioms leaf00720_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
