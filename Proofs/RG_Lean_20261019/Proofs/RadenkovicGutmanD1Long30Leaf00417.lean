/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00417 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 147689989185241971081434313523200000000000 103819940882746063425479228766710793240576 648364824784970489036898566144000000000000))
theorem leaf00417_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 147689989185241971081434313523200000000000 103819940882746063425479228766710793240576 648364824784970489036898566144000000000000 raw00417=true := by decide +kernel
#print axioms leaf00417_raw
theorem leaf00417_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00417=true := by decide +kernel
#print axioms leaf00417_rectangular
def affine00417 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00417 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00417_transform : affine00417=(NestedInteger.clearedAll 3 raw00417 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00417_transform
theorem leaf00417_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00417=true := by decide +kernel
#print axioms leaf00417_sign
theorem leaf00417_log : RationalLog.accepts (1301231285/2147483648) (-1075858853/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00417_log
def leaf00417 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (160125807129/1000000000000) (1301231285/2147483648) (-1075858853/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00417
theorem leaf00417_checked : FastNestedCellData.accepts 1 2 4 leaf00417=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (160125807129/1000000000000) (1301231285/2147483648) (-1075858853/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/8)] ![(1/6400),1,(1/8)] 147689989185241971081434313523200000000000 103819940882746063425479228766710793240576 648364824784970489036898566144000000000000 raw00417 affine00417
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00417_raw leaf00417_rectangular
    leaf00417_transform leaf00417_sign leaf00417_log
#print axioms leaf00417_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
