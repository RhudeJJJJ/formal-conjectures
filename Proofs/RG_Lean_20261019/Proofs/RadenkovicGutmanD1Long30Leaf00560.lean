/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00560 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3734672410158019850658425864192000000000000 39760109351375675118894223135676659924992 49096981006461271446078357504000000000000))
theorem leaf00560_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3734672410158019850658425864192000000000000 39760109351375675118894223135676659924992 49096981006461271446078357504000000000000 raw00560=true := by decide +kernel
#print axioms leaf00560_raw
theorem leaf00560_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00560=true := by decide +kernel
#print axioms leaf00560_rectangular
def affine00560 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00560 (IntegerComputedClassCell.leftNumerator ![(11/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/640),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00560_transform : affine00560=(NestedInteger.clearedAll 3 raw00560 (IntegerComputedClassCell.leftNumerator ![(11/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/640),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00560_transform
theorem leaf00560_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00560=true := by decide +kernel
#print axioms leaf00560_sign
theorem leaf00560_log : RationalLog.accepts (12632451/2147483648) (-1378626303/536870912) 8 8=true := by decide +kernel
#print axioms leaf00560_log
def leaf00560 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (809827988123/1000000000000) (12632451/2147483648) (-1378626303/536870912) 8 8 ![60,0,4] ![(11/640),0,0] ![(1/3200),1,(1/16)] affine00560
theorem leaf00560_checked : FastNestedCellData.accepts 1 2 4 leaf00560=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (809827988123/1000000000000) (12632451/2147483648) (-1378626303/536870912) 8 8 ![60,0,4] ![(11/640),0,0] ![(1/3200),1,(1/16)] 3734672410158019850658425864192000000000000 39760109351375675118894223135676659924992 49096981006461271446078357504000000000000 raw00560 affine00560
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00560_raw leaf00560_rectangular
    leaf00560_transform leaf00560_sign leaf00560_log
#print axioms leaf00560_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
