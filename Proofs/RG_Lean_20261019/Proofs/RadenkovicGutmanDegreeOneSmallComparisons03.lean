/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum016
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum018
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum019
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum020
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum021
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum025
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum026
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum035
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum042
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum051
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum059
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum060
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum068
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum079
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum085
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum086
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum089
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum097
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1015
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum124
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1288
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum136
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1452
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1467
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1512
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum167
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum194
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum197
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum214
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum217
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum222
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum227
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum249
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum346
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum373
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum382
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum389
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum397
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum405
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum491
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum498
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum552
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum559
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum563
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum564
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum888
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum894
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum930
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum935
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum967
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum977
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0150 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum042.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum068.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum068.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum042.actual_graph_bounds.2
  linarith
#print axioms comparison0150
theorem comparison0151 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum097.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum097.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0151
theorem comparison0152 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum249.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum249.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0152
theorem comparison0153 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum405.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum405.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0153
theorem comparison0154 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1015.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1015.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0154
theorem comparison0155 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum346.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum346.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0155
theorem comparison0156 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum564.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum564.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0156
theorem comparison0157 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1467.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1467.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0157
theorem comparison0158 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1512.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1512.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0158
theorem comparison0159 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum016.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum021.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0159
theorem comparison0160 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum035.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0160
theorem comparison0161 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum090.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0161
theorem comparison0162 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum167.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum167.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0162
theorem comparison0163 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum397.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0163
theorem comparison0164 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum860.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0164
theorem comparison0165 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum081.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0165
theorem comparison0166 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum222.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum222.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0166
theorem comparison0167 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum393.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0167
theorem comparison0168 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum977.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum977.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0168
theorem comparison0169 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum563.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum563.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0169
theorem comparison0170 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum967.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum967.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0170
theorem comparison0171 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum021.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum019.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum019.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum021.actual_graph_bounds.2
  linarith
#print axioms comparison0171
theorem comparison0172 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum051.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum051.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0172
theorem comparison0173 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum079.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum079.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0173
theorem comparison0174 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum197.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum197.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0174
theorem comparison0175 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum373.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0175
theorem comparison0176 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum894.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0176
theorem comparison0177 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum124.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum124.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0177
theorem comparison0178 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum194.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum194.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0178
theorem comparison0179 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum498.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum498.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0179
theorem comparison0180 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum888.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum888.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0180
theorem comparison0181 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum491.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum491.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0181
theorem comparison0182 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1288.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1288.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0182
theorem comparison0183 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum025.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum020.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum020.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum025.actual_graph_bounds.2
  linarith
#print axioms comparison0183
theorem comparison0184 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum059.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum059.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum035.actual_graph_bounds.2
  linarith
#print axioms comparison0184
theorem comparison0185 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum085.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum085.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0185
theorem comparison0186 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum217.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum217.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0186
theorem comparison0187 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum382.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0187
theorem comparison0188 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum935.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0188
theorem comparison0189 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum136.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum136.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0189
theorem comparison0190 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum214.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum214.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0190
theorem comparison0191 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum559.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum559.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0191
theorem comparison0192 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum930.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum930.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0192
theorem comparison0193 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum552.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum552.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0193
theorem comparison0194 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1452.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1452.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0194
theorem comparison0195 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum026.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum018.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum018.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum026.actual_graph_bounds.2
  linarith
#print axioms comparison0195
theorem comparison0196 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum060.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum060.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum036.actual_graph_bounds.2
  linarith
#print axioms comparison0196
theorem comparison0197 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum089.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum089.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison0197
theorem comparison0198 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum227.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum227.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0198
theorem comparison0199 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum389.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0199
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
