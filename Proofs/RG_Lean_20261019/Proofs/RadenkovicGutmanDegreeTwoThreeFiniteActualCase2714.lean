/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2714 : Family 10 := level10.get ⟨860,by decide⟩
def sourceMap2714 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2714 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2714_checked : acceptsGraphIso
    (source (graph core2714) (root 10) 0 4) DegreeTwoThreeSpectrum6913.graph sourceMap2714=true := by decide +kernel
theorem fusedMap2714_checked : acceptsGraphIso
    (fused (graph core2714) (root 10) 0 4) DegreeTwoThreeSpectrum5696.graph fusedMap2714=true := by decide +kernel
theorem certified2714 : Certified (graph core2714) (root 10) 0 4 :=
  of_native_maps core2714 DegreeTwoThreeSpectrum6913.graph DegreeTwoThreeSpectrum5696.graph
    sourceMap2714 fusedMap2714 sourceMap2714_checked fusedMap2714_checked
    DegreeTwoThreeFiniteComparisons.comparison2714
#print axioms sourceMap2714_checked
#print axioms fusedMap2714_checked
#print axioms certified2714
def sourceMap2714swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2714swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2714swap_checked : acceptsGraphIso
    (source (graph core2714) (root 10) 4 0) DegreeTwoThreeSpectrum6913.graph sourceMap2714swap=true := by decide +kernel
theorem fusedMap2714swap_checked : acceptsGraphIso
    (fused (graph core2714) (root 10) 4 0) DegreeTwoThreeSpectrum5696.graph fusedMap2714swap=true := by decide +kernel
theorem certified2714swap : Certified (graph core2714) (root 10) 4 0 :=
  of_native_maps core2714 DegreeTwoThreeSpectrum6913.graph DegreeTwoThreeSpectrum5696.graph
    sourceMap2714swap fusedMap2714swap sourceMap2714swap_checked fusedMap2714swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2714
#print axioms sourceMap2714swap_checked
#print axioms fusedMap2714swap_checked
#print axioms certified2714swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
