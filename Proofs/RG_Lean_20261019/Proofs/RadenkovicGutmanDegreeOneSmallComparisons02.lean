/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum008
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum009
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum011
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum012
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum013
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum014
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum017
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum020
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum024
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum025
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum030
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum035
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum039
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum042
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum049
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum052
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum054
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum055
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum060
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum076
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum083
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum086
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum087
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum101
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1189
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum128
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1398
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum144
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1508
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1509
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1510
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum170
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum183
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum188
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum208
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum212
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum218
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum228
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum312
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum341
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum411
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum458
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum464
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum535
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum540
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum585
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum863
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum880
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum923
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum929
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum967
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0100 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum396.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0100
theorem comparison0101 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum859.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0101
theorem comparison0102 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum055.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum055.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0102
theorem comparison0103 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum087.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum087.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0103
theorem comparison0104 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum228.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum228.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0104
theorem comparison0105 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum393.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0105
theorem comparison0106 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum971.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0106
theorem comparison0107 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum218.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum218.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0107
theorem comparison0108 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum585.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum585.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0108
theorem comparison0109 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum967.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum967.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0109
theorem comparison0110 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1508.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1508.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0110
theorem comparison0111 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum008.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum013.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum013.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum008.actual_graph_bounds.2
  linarith
#print axioms comparison0111
theorem comparison0112 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum020.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum020.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum021.actual_graph_bounds.2
  linarith
#print axioms comparison0112
theorem comparison0113 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum052.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum052.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0113
theorem comparison0114 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum076.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum076.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0114
theorem comparison0115 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum188.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum188.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0115
theorem comparison0116 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum372.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0116
theorem comparison0117 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum887.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0117
theorem comparison0118 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum049.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum049.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0118
theorem comparison0119 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum128.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum128.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0119
theorem comparison0120 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum183.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum183.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0120
theorem comparison0121 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum464.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum464.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0121
theorem comparison0122 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum880.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum880.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0122
theorem comparison0123 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum312.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum312.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0123
theorem comparison0124 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum458.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum458.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0124
theorem comparison0125 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1189.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1189.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0125
theorem comparison0126 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1509.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1509.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0126
theorem comparison0127 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum009.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum014.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum014.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum009.actual_graph_bounds.2
  linarith
#print axioms comparison0127
theorem comparison0128 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum025.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum024.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum024.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum025.actual_graph_bounds.2
  linarith
#print axioms comparison0128
theorem comparison0129 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum060.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum060.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum035.actual_graph_bounds.2
  linarith
#print axioms comparison0129
theorem comparison0130 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum083.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum083.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0130
theorem comparison0131 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum212.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum212.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0131
theorem comparison0132 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum381.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0132
theorem comparison0133 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum929.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0133
theorem comparison0134 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum054.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum054.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum035.actual_graph_bounds.2
  linarith
#print axioms comparison0134
theorem comparison0135 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum144.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum144.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0135
theorem comparison0136 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum208.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum208.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0136
theorem comparison0137 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum540.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum540.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0137
theorem comparison0138 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum923.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum923.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0138
theorem comparison0139 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum341.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum341.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0139
theorem comparison0140 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum535.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum535.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0140
theorem comparison0141 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1398.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1398.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0141
theorem comparison0142 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1510.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1510.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0142
theorem comparison0143 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum012.graph) (2-2/7) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum011.graph) (2-2/7) := by
  have hs := DegreeOneSmallSpectrum011.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum012.actual_graph_bounds.2
  linarith
#print axioms comparison0143
theorem comparison0144 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum017.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum030.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum030.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison0144
theorem comparison0145 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum042.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum039.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum039.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum042.actual_graph_bounds.2
  linarith
#print axioms comparison0145
theorem comparison0146 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum101.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum101.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0146
theorem comparison0147 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum170.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum170.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0147
theorem comparison0148 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum411.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum411.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0148
theorem comparison0149 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum863.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum863.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0149
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
