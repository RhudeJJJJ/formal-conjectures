/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2575 : Family 10 := level10.get ⟨460,by decide⟩
def sourceMap2575 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2575 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2575_checked : acceptsGraphIso
    (source (graph core2575) (root 10) 0 4) DegreeTwoThreeSpectrum5896.graph sourceMap2575=true := by decide +kernel
theorem fusedMap2575_checked : acceptsGraphIso
    (fused (graph core2575) (root 10) 0 4) DegreeTwoThreeSpectrum5897.graph fusedMap2575=true := by decide +kernel
theorem certified2575 : Certified (graph core2575) (root 10) 0 4 :=
  of_native_maps core2575 DegreeTwoThreeSpectrum5896.graph DegreeTwoThreeSpectrum5897.graph
    sourceMap2575 fusedMap2575 sourceMap2575_checked fusedMap2575_checked
    DegreeTwoThreeFiniteComparisons.comparison2575
#print axioms sourceMap2575_checked
#print axioms fusedMap2575_checked
#print axioms certified2575
def sourceMap2575swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2575swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2575swap_checked : acceptsGraphIso
    (source (graph core2575) (root 10) 4 0) DegreeTwoThreeSpectrum5896.graph sourceMap2575swap=true := by decide +kernel
theorem fusedMap2575swap_checked : acceptsGraphIso
    (fused (graph core2575) (root 10) 4 0) DegreeTwoThreeSpectrum5897.graph fusedMap2575swap=true := by decide +kernel
theorem certified2575swap : Certified (graph core2575) (root 10) 4 0 :=
  of_native_maps core2575 DegreeTwoThreeSpectrum5896.graph DegreeTwoThreeSpectrum5897.graph
    sourceMap2575swap fusedMap2575swap sourceMap2575swap_checked fusedMap2575swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2575
#print axioms sourceMap2575swap_checked
#print axioms fusedMap2575swap_checked
#print axioms certified2575swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
