/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00883 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 665869556443037062903365632000000000 353969340345893915453004275458768896 957626714636395117490995200000000000))
theorem leaf00883_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 665869556443037062903365632000000000 353969340345893915453004275458768896 957626714636395117490995200000000000 raw00883=true := by decide +kernel
#print axioms leaf00883_raw
theorem leaf00883_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00883=true := by decide +kernel
#print axioms leaf00883_rectangular
def affine00883 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00883 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00883_transform : affine00883=(NestedInteger.clearedAll 3 raw00883 (IntegerComputedClassCell.leftNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00883_transform
theorem leaf00883_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00883=true := by decide +kernel
#print axioms leaf00883_sign
theorem leaf00883_log : RationalLog.accepts (416747025/1073741824) (-254054163/536870912) 2 8=true := by decide +kernel
#print axioms leaf00883_log
def leaf00883 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2310199103/6250000000) (416747025/1073741824) (-254054163/536870912) 2 8 ![60,0,4] ![(1/16),0,(1/4)] ![(1/640),1,(1/4)] affine00883
theorem leaf00883_checked : FastNestedCellData.accepts 1 2 4 leaf00883=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2310199103/6250000000) (416747025/1073741824) (-254054163/536870912) 2 8 ![60,0,4] ![(1/16),0,(1/4)] ![(1/640),1,(1/4)] 665869556443037062903365632000000000 353969340345893915453004275458768896 957626714636395117490995200000000000 raw00883 affine00883
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00883_raw leaf00883_rectangular
    leaf00883_transform leaf00883_sign leaf00883_log
#print axioms leaf00883_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
