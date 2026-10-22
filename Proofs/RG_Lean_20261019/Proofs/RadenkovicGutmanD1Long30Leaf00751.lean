/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00751 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 186977952687449859590031671296000000000000 48787322733284203772946428866883567484928 75206665709701707519640993792000000000000))
theorem leaf00751_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 186977952687449859590031671296000000000000 48787322733284203772946428866883567484928 75206665709701707519640993792000000000000 raw00751=true := by decide +kernel
#print axioms leaf00751_raw
theorem leaf00751_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00751=true := by decide +kernel
#print axioms leaf00751_rectangular
def affine00751 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00751 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00751_transform : affine00751=(NestedInteger.clearedAll 3 raw00751 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00751_transform
theorem leaf00751_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00751=true := by decide +kernel
#print axioms leaf00751_sign
theorem leaf00751_log : RationalLog.accepts (169930823/1073741824) (-494864381/536870912) 3 8=true := by decide +kernel
#print axioms leaf00751_log
def leaf00751 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (324355044017/500000000000) (169930823/1073741824) (-494864381/536870912) 3 8 ![60,0,4] ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)] affine00751
theorem leaf00751_checked : FastNestedCellData.accepts 1 2 4 leaf00751=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (324355044017/500000000000) (169930823/1073741824) (-494864381/536870912) 3 8 ![60,0,4] ![(43/1280),0,(1/16)] ![(3/6400),1,(1/16)] 186977952687449859590031671296000000000000 48787322733284203772946428866883567484928 75206665709701707519640993792000000000000 raw00751 affine00751
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00751_raw leaf00751_rectangular
    leaf00751_transform leaf00751_sign leaf00751_log
#print axioms leaf00751_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
