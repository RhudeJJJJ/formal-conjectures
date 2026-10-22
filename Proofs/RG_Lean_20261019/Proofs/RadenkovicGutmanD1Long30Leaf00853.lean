/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00853 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 24161923104429345488022536192000000000000 13177486139499407430042320801276375334912 39298939185283721717084061696000000000000))
theorem leaf00853_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 24161923104429345488022536192000000000000 13177486139499407430042320801276375334912 39298939185283721717084061696000000000000 raw00853=true := by decide +kernel
#print axioms leaf00853_raw
theorem leaf00853_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00853=true := by decide +kernel
#print axioms leaf00853_rectangular
def affine00853 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00853 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00853_transform : affine00853=(NestedInteger.clearedAll 3 raw00853 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00853_transform
theorem leaf00853_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00853=true := by decide +kernel
#print axioms leaf00853_sign
theorem leaf00853_log : RationalLog.accepts (1754193573/4294967296) (-961465715/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00853_log
def leaf00853 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20957127617/62500000000) (1754193573/4294967296) (-961465715/2147483648) 2 8 ![60,0,4] ![(17/320),0,(1/4)] ![(1/640),1,(1/4)] affine00853
theorem leaf00853_checked : FastNestedCellData.accepts 1 2 4 leaf00853=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20957127617/62500000000) (1754193573/4294967296) (-961465715/2147483648) 2 8 ![60,0,4] ![(17/320),0,(1/4)] ![(1/640),1,(1/4)] 24161923104429345488022536192000000000000 13177486139499407430042320801276375334912 39298939185283721717084061696000000000000 raw00853 affine00853
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00853_raw leaf00853_rectangular
    leaf00853_transform leaf00853_sign leaf00853_log
#print axioms leaf00853_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
