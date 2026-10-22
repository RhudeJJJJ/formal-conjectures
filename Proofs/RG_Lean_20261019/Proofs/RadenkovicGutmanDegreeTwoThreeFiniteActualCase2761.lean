/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2761 : Family 10 := level10.get ⟨970,by decide⟩
def sourceMap2761 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2761 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2761_checked : acceptsGraphIso
    (source (graph core2761) (root 10) 0 4) DegreeTwoThreeSpectrum7040.graph sourceMap2761=true := by decide +kernel
theorem fusedMap2761_checked : acceptsGraphIso
    (fused (graph core2761) (root 10) 0 4) DegreeTwoThreeSpectrum5890.graph fusedMap2761=true := by decide +kernel
theorem certified2761 : Certified (graph core2761) (root 10) 0 4 :=
  of_native_maps core2761 DegreeTwoThreeSpectrum7040.graph DegreeTwoThreeSpectrum5890.graph
    sourceMap2761 fusedMap2761 sourceMap2761_checked fusedMap2761_checked
    DegreeTwoThreeFiniteComparisons.comparison2761
#print axioms sourceMap2761_checked
#print axioms fusedMap2761_checked
#print axioms certified2761
def sourceMap2761swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2761swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2761swap_checked : acceptsGraphIso
    (source (graph core2761) (root 10) 4 0) DegreeTwoThreeSpectrum7040.graph sourceMap2761swap=true := by decide +kernel
theorem fusedMap2761swap_checked : acceptsGraphIso
    (fused (graph core2761) (root 10) 4 0) DegreeTwoThreeSpectrum5890.graph fusedMap2761swap=true := by decide +kernel
theorem certified2761swap : Certified (graph core2761) (root 10) 4 0 :=
  of_native_maps core2761 DegreeTwoThreeSpectrum7040.graph DegreeTwoThreeSpectrum5890.graph
    sourceMap2761swap fusedMap2761swap sourceMap2761swap_checked fusedMap2761swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2761
#print axioms sourceMap2761swap_checked
#print axioms fusedMap2761swap_checked
#print axioms certified2761swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
