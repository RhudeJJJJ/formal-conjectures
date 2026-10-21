/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum004
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum005
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum006
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum008
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum009
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum010
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum014
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum016
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum018
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum022
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum025
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum026
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum032
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum043
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum047
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum061
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum075
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum087
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum091
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum111
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum146
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum147
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum176
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum218
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum219
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum228
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum434
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum563
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum567
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum585
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum586
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum871
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum945
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum946
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum967
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum968
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum977
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0050 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum951.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0050
theorem comparison0051 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum228.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum228.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0051
theorem comparison0052 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum393.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0052
theorem comparison0053 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum971.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0053
theorem comparison0054 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum977.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum977.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0054
theorem comparison0055 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum004.graph) (2-2/6) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum006.graph) (2-2/6) := by
  have hs := DegreeOneSmallSpectrum006.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum004.actual_graph_bounds.2
  linarith
#print axioms comparison0055
theorem comparison0056 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum009.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum009.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0056
theorem comparison0057 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum026.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum026.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0057
theorem comparison0058 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum036.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0058
theorem comparison0059 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum090.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0059
theorem comparison0060 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum166.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0060
theorem comparison0061 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum392.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0061
theorem comparison0062 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum858.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0062
theorem comparison0063 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum022.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum022.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0063
theorem comparison0064 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum061.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum061.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0064
theorem comparison0065 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum087.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0065
theorem comparison0066 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum222.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0066
theorem comparison0067 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum387.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0067
theorem comparison0068 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum951.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0068
theorem comparison0069 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum146.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum146.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0069
theorem comparison0070 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum218.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum218.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0070
theorem comparison0071 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum563.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum563.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0071
theorem comparison0072 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum945.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum945.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0072
theorem comparison0073 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum585.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum585.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0073
theorem comparison0074 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum967.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum967.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0074
theorem comparison0075 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum006.graph) (2-2/6) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum005.graph) (2-2/6) := by
  have hs := DegreeOneSmallSpectrum005.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum006.actual_graph_bounds.2
  linarith
#print axioms comparison0075
theorem comparison0076 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum008.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum014.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum014.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum008.actual_graph_bounds.2
  linarith
#print axioms comparison0076
theorem comparison0077 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum018.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum018.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum021.actual_graph_bounds.2
  linarith
#print axioms comparison0077
theorem comparison0078 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum047.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum047.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0078
theorem comparison0079 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum075.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0079
theorem comparison0080 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum182.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0080
theorem comparison0081 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum371.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0081
theorem comparison0082 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum879.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0082
theorem comparison0083 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum032.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum032.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum021.actual_graph_bounds.2
  linarith
#print axioms comparison0083
theorem comparison0084 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum043.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum043.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0084
theorem comparison0085 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum111.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum111.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0085
theorem comparison0086 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum176.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum176.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0086
theorem comparison0087 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum434.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum434.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0087
theorem comparison0088 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum871.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum871.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0088
theorem comparison0089 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum147.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum147.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0089
theorem comparison0090 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum219.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum219.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0090
theorem comparison0091 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum567.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum567.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0091
theorem comparison0092 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum946.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum946.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0092
theorem comparison0093 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum586.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum586.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0093
theorem comparison0094 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum968.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum968.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0094
theorem comparison0095 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum010.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum008.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum008.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum010.actual_graph_bounds.2
  linarith
#print axioms comparison0095
theorem comparison0096 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum025.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum025.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0096
theorem comparison0097 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum036.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0097
theorem comparison0098 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum091.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum091.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0098
theorem comparison0099 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum167.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0099
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
