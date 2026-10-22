/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2710 : Family 10 := level10.get ⟨849,by decide⟩
def sourceMap2710 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2710 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2710_checked : acceptsGraphIso
    (source (graph core2710) (root 10) 0 4) DegreeTwoThreeSpectrum6894.graph sourceMap2710=true := by decide +kernel
theorem fusedMap2710_checked : acceptsGraphIso
    (fused (graph core2710) (root 10) 0 4) DegreeTwoThreeSpectrum5682.graph fusedMap2710=true := by decide +kernel
theorem certified2710 : Certified (graph core2710) (root 10) 0 4 :=
  of_native_maps core2710 DegreeTwoThreeSpectrum6894.graph DegreeTwoThreeSpectrum5682.graph
    sourceMap2710 fusedMap2710 sourceMap2710_checked fusedMap2710_checked
    DegreeTwoThreeFiniteComparisons.comparison2710
#print axioms sourceMap2710_checked
#print axioms fusedMap2710_checked
#print axioms certified2710
def sourceMap2710swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2710swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2710swap_checked : acceptsGraphIso
    (source (graph core2710) (root 10) 4 0) DegreeTwoThreeSpectrum6894.graph sourceMap2710swap=true := by decide +kernel
theorem fusedMap2710swap_checked : acceptsGraphIso
    (fused (graph core2710) (root 10) 4 0) DegreeTwoThreeSpectrum5682.graph fusedMap2710swap=true := by decide +kernel
theorem certified2710swap : Certified (graph core2710) (root 10) 4 0 :=
  of_native_maps core2710 DegreeTwoThreeSpectrum6894.graph DegreeTwoThreeSpectrum5682.graph
    sourceMap2710swap fusedMap2710swap sourceMap2710swap_checked fusedMap2710swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2710
#print axioms sourceMap2710swap_checked
#print axioms fusedMap2710swap_checked
#print axioms certified2710swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
