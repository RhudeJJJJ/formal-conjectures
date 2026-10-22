/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2982 : Family 10 := level10.get ⟨1528,by decide⟩
def sourceMap2982 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2982 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2982_checked : acceptsGraphIso
    (source (graph core2982) (root 10) 0 4) DegreeTwoThreeSpectrum7066.graph sourceMap2982=true := by decide +kernel
theorem fusedMap2982_checked : acceptsGraphIso
    (fused (graph core2982) (root 10) 0 4) DegreeTwoThreeSpectrum5964.graph fusedMap2982=true := by decide +kernel
theorem certified2982 : Certified (graph core2982) (root 10) 0 4 :=
  of_native_maps core2982 DegreeTwoThreeSpectrum7066.graph DegreeTwoThreeSpectrum5964.graph
    sourceMap2982 fusedMap2982 sourceMap2982_checked fusedMap2982_checked
    DegreeTwoThreeFiniteComparisons.comparison2982
#print axioms sourceMap2982_checked
#print axioms fusedMap2982_checked
#print axioms certified2982
def sourceMap2982swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2982swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2982swap_checked : acceptsGraphIso
    (source (graph core2982) (root 10) 4 0) DegreeTwoThreeSpectrum7066.graph sourceMap2982swap=true := by decide +kernel
theorem fusedMap2982swap_checked : acceptsGraphIso
    (fused (graph core2982) (root 10) 4 0) DegreeTwoThreeSpectrum5964.graph fusedMap2982swap=true := by decide +kernel
theorem certified2982swap : Certified (graph core2982) (root 10) 4 0 :=
  of_native_maps core2982 DegreeTwoThreeSpectrum7066.graph DegreeTwoThreeSpectrum5964.graph
    sourceMap2982swap fusedMap2982swap sourceMap2982swap_checked fusedMap2982swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2982
#print axioms sourceMap2982swap_checked
#print axioms fusedMap2982swap_checked
#print axioms certified2982swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
