/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0050
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0051
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0052
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0053
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0054
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0055
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0056
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0057
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0058
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0059
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0060
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0061
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0062
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0063
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0064
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0065
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0066
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0067
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0068
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0069
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0070
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0071
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0072
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0073
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0074
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0075
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0076
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0077
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0078
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0079
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0080
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0081
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0082
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0083
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0084
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0085
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0086
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0087
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0088
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0089
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0090
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0091
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0092
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0093
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0094
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0095
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0096
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0097
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0098
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0099
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys01 : ∀ k ∈ keys01, Certified k := by
  apply certified_cons (by exact certified0050)
  apply certified_cons (by exact certified0050swap)
  apply certified_cons (by exact certified0051)
  apply certified_cons (by exact certified0052)
  apply certified_cons (by exact certified0052swap)
  apply certified_cons (by exact certified0053)
  apply certified_cons (by exact certified0053swap)
  apply certified_cons (by exact certified0054)
  apply certified_cons (by exact certified0055)
  apply certified_cons (by exact certified0056)
  apply certified_cons (by exact certified0056swap)
  apply certified_cons (by exact certified0057)
  apply certified_cons (by exact certified0057swap)
  apply certified_cons (by exact certified0058)
  apply certified_cons (by exact certified0058swap)
  apply certified_cons (by exact certified0059)
  apply certified_cons (by exact certified0059swap)
  apply certified_cons (by exact certified0060)
  apply certified_cons (by exact certified0060swap)
  apply certified_cons (by exact certified0061)
  apply certified_cons (by exact certified0061swap)
  apply certified_cons (by exact certified0062)
  apply certified_cons (by exact certified0062swap)
  apply certified_cons (by exact certified0063)
  apply certified_cons (by exact certified0064)
  apply certified_cons (by exact certified0064swap)
  apply certified_cons (by exact certified0065)
  apply certified_cons (by exact certified0065swap)
  apply certified_cons (by exact certified0066)
  apply certified_cons (by exact certified0066swap)
  apply certified_cons (by exact certified0067)
  apply certified_cons (by exact certified0067swap)
  apply certified_cons (by exact certified0068)
  apply certified_cons (by exact certified0068swap)
  apply certified_cons (by exact certified0069)
  apply certified_cons (by exact certified0070)
  apply certified_cons (by exact certified0070swap)
  apply certified_cons (by exact certified0071)
  apply certified_cons (by exact certified0071swap)
  apply certified_cons (by exact certified0072)
  apply certified_cons (by exact certified0072swap)
  apply certified_cons (by exact certified0073)
  apply certified_cons (by exact certified0074)
  apply certified_cons (by exact certified0074swap)
  apply certified_cons (by exact certified0075)
  apply certified_cons (by exact certified0076)
  apply certified_cons (by exact certified0076swap)
  apply certified_cons (by exact certified0077)
  apply certified_cons (by exact certified0077swap)
  apply certified_cons (by exact certified0078)
  apply certified_cons (by exact certified0078swap)
  apply certified_cons (by exact certified0079)
  apply certified_cons (by exact certified0079swap)
  apply certified_cons (by exact certified0080)
  apply certified_cons (by exact certified0080swap)
  apply certified_cons (by exact certified0081)
  apply certified_cons (by exact certified0081swap)
  apply certified_cons (by exact certified0082)
  apply certified_cons (by exact certified0082swap)
  apply certified_cons (by exact certified0083)
  apply certified_cons (by exact certified0084)
  apply certified_cons (by exact certified0084swap)
  apply certified_cons (by exact certified0085)
  apply certified_cons (by exact certified0085swap)
  apply certified_cons (by exact certified0086)
  apply certified_cons (by exact certified0086swap)
  apply certified_cons (by exact certified0087)
  apply certified_cons (by exact certified0087swap)
  apply certified_cons (by exact certified0088)
  apply certified_cons (by exact certified0088swap)
  apply certified_cons (by exact certified0089)
  apply certified_cons (by exact certified0090)
  apply certified_cons (by exact certified0090swap)
  apply certified_cons (by exact certified0091)
  apply certified_cons (by exact certified0091swap)
  apply certified_cons (by exact certified0092)
  apply certified_cons (by exact certified0092swap)
  apply certified_cons (by exact certified0093)
  apply certified_cons (by exact certified0094)
  apply certified_cons (by exact certified0094swap)
  apply certified_cons (by exact certified0095)
  apply certified_cons (by exact certified0096)
  apply certified_cons (by exact certified0096swap)
  apply certified_cons (by exact certified0097)
  apply certified_cons (by exact certified0097swap)
  apply certified_cons (by exact certified0098)
  apply certified_cons (by exact certified0098swap)
  apply certified_cons (by exact certified0099)
  apply certified_cons (by exact certified0099swap)
  simp
#print axioms certified_keys01
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
