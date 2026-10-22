/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2594 : Family 10 := level10.get ⟨513,by decide⟩
def sourceMap2594 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2594 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2594_checked : acceptsGraphIso
    (source (graph core2594) (root 10) 0 4) DegreeTwoThreeSpectrum6042.graph sourceMap2594=true := by decide +kernel
theorem fusedMap2594_checked : acceptsGraphIso
    (fused (graph core2594) (root 10) 0 4) DegreeTwoThreeSpectrum5152.graph fusedMap2594=true := by decide +kernel
theorem certified2594 : Certified (graph core2594) (root 10) 0 4 :=
  of_native_maps core2594 DegreeTwoThreeSpectrum6042.graph DegreeTwoThreeSpectrum5152.graph
    sourceMap2594 fusedMap2594 sourceMap2594_checked fusedMap2594_checked
    DegreeTwoThreeFiniteComparisons.comparison2594
#print axioms sourceMap2594_checked
#print axioms fusedMap2594_checked
#print axioms certified2594
def sourceMap2594swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2594swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2594swap_checked : acceptsGraphIso
    (source (graph core2594) (root 10) 4 0) DegreeTwoThreeSpectrum6042.graph sourceMap2594swap=true := by decide +kernel
theorem fusedMap2594swap_checked : acceptsGraphIso
    (fused (graph core2594) (root 10) 4 0) DegreeTwoThreeSpectrum5152.graph fusedMap2594swap=true := by decide +kernel
theorem certified2594swap : Certified (graph core2594) (root 10) 4 0 :=
  of_native_maps core2594 DegreeTwoThreeSpectrum6042.graph DegreeTwoThreeSpectrum5152.graph
    sourceMap2594swap fusedMap2594swap sourceMap2594swap_checked fusedMap2594swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2594
#print axioms sourceMap2594swap_checked
#print axioms fusedMap2594swap_checked
#print axioms certified2594swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
