/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00443 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 2064934081775170385256382464000000000000 2274736723590876098803712179353874857984 317515327619110609647162097664000000000000))
theorem leaf00443_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 2064934081775170385256382464000000000000 2274736723590876098803712179353874857984 317515327619110609647162097664000000000000 raw00443=true := by decide +kernel
#print axioms leaf00443_raw
theorem leaf00443_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00443=true := by decide +kernel
#print axioms leaf00443_rectangular
def affine00443 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00443 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00443_transform : affine00443=(NestedInteger.clearedAll 3 raw00443 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00443_transform
theorem leaf00443_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00443=true := by decide +kernel
#print axioms leaf00443_sign
theorem leaf00443_log : RationalLog.accepts (4697691971/4294967296) (96236663/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00443_log
def leaf00443 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (895522407/125000000000) (4697691971/4294967296) (96236663/2147483648) 0 8 ![52,0,4] ![(1/4),0,(3/4)] ![(1/64),1,(1/4)] affine00443
theorem leaf00443_checked : FastNestedCellData.accepts 1 0 4 leaf00443=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (895522407/125000000000) (4697691971/4294967296) (96236663/2147483648) 0 8 ![52,0,4] ![(1/4),0,(3/4)] ![(1/64),1,(1/4)] 2064934081775170385256382464000000000000 2274736723590876098803712179353874857984 317515327619110609647162097664000000000000 raw00443 affine00443
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00443_raw leaf00443_rectangular
    leaf00443_transform leaf00443_sign leaf00443_log
#print axioms leaf00443_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
