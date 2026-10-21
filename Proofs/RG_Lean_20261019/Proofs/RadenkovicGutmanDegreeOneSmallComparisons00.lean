/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum000
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum001
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum002
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum003
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum004
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum006
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum007
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum008
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum009
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum010
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum015
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum016
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum022
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum025
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum026
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum035
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum055
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum061
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum086
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum087
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum091
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum397
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0000 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum000.graph) (2-2/4) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum001.graph) (2-2/4) := by
  have hs := DegreeOneSmallSpectrum001.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum000.actual_graph_bounds.2
  linarith
#print axioms comparison0000
theorem comparison0001 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum003.graph) (2-2/5) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum002.graph) (2-2/5) := by
  have hs := DegreeOneSmallSpectrum002.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum003.actual_graph_bounds.2
  linarith
#print axioms comparison0001
theorem comparison0002 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum004.graph) (2-2/6) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum006.graph) (2-2/6) := by
  have hs := DegreeOneSmallSpectrum006.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum004.actual_graph_bounds.2
  linarith
#print axioms comparison0002
theorem comparison0003 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum008.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum008.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0003
theorem comparison0004 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum021.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0004
theorem comparison0005 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum034.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0005
theorem comparison0006 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum080.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0006
theorem comparison0007 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum164.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0007
theorem comparison0008 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum378.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0008
theorem comparison0009 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum856.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0009
theorem comparison0010 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum004.graph) (2-2/6) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum007.graph) (2-2/6) := by
  have hs := DegreeOneSmallSpectrum007.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum004.actual_graph_bounds.2
  linarith
#print axioms comparison0010
theorem comparison0011 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum009.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum009.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0011
theorem comparison0012 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum025.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum025.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0012
theorem comparison0013 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum035.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0013
theorem comparison0014 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum086.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0014
theorem comparison0015 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum165.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0015
theorem comparison0016 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum386.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0016
theorem comparison0017 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum857.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0017
theorem comparison0018 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum026.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum026.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0018
theorem comparison0019 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum036.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0019
theorem comparison0020 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum090.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0020
theorem comparison0021 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum166.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0021
theorem comparison0022 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum392.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0022
theorem comparison0023 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum858.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0023
theorem comparison0024 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum091.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum091.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0024
theorem comparison0025 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum167.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0025
theorem comparison0026 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum396.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0026
theorem comparison0027 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum859.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0027
theorem comparison0028 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum397.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0028
theorem comparison0029 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum860.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0029
theorem comparison0030 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum003.graph) (2-2/5) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum002.graph) (2-2/5) := by
  have hs := DegreeOneSmallSpectrum002.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum003.actual_graph_bounds.2
  linarith
#print axioms comparison0030
theorem comparison0031 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum004.graph) (2-2/6) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum007.graph) (2-2/6) := by
  have hs := DegreeOneSmallSpectrum007.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum004.actual_graph_bounds.2
  linarith
#print axioms comparison0031
theorem comparison0032 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum009.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum009.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0032
theorem comparison0033 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum025.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum025.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0033
theorem comparison0034 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum035.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0034
theorem comparison0035 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum086.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0035
theorem comparison0036 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum165.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0036
theorem comparison0037 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum386.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0037
theorem comparison0038 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum857.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0038
theorem comparison0039 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum015.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum015.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0039
theorem comparison0040 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum022.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum022.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0040
theorem comparison0041 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum055.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum055.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0041
theorem comparison0042 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum081.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0042
theorem comparison0043 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum202.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0043
theorem comparison0044 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum379.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0044
theorem comparison0045 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum915.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0045
theorem comparison0046 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum061.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum061.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0046
theorem comparison0047 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum087.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0047
theorem comparison0048 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum222.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0048
theorem comparison0049 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum387.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0049
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
