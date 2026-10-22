/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2693 : Family 10 := level10.get ⟨804,by decide⟩
def sourceMap2693 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2693 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2693_checked : acceptsGraphIso
    (source (graph core2693) (root 10) 0 4) DegreeTwoThreeSpectrum6765.graph sourceMap2693=true := by decide +kernel
theorem fusedMap2693_checked : acceptsGraphIso
    (fused (graph core2693) (root 10) 0 4) DegreeTwoThreeSpectrum5600.graph fusedMap2693=true := by decide +kernel
theorem certified2693 : Certified (graph core2693) (root 10) 0 4 :=
  of_native_maps core2693 DegreeTwoThreeSpectrum6765.graph DegreeTwoThreeSpectrum5600.graph
    sourceMap2693 fusedMap2693 sourceMap2693_checked fusedMap2693_checked
    DegreeTwoThreeFiniteComparisons.comparison2693
#print axioms sourceMap2693_checked
#print axioms fusedMap2693_checked
#print axioms certified2693
def sourceMap2693swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2693swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2693swap_checked : acceptsGraphIso
    (source (graph core2693) (root 10) 4 0) DegreeTwoThreeSpectrum6765.graph sourceMap2693swap=true := by decide +kernel
theorem fusedMap2693swap_checked : acceptsGraphIso
    (fused (graph core2693) (root 10) 4 0) DegreeTwoThreeSpectrum5600.graph fusedMap2693swap=true := by decide +kernel
theorem certified2693swap : Certified (graph core2693) (root 10) 4 0 :=
  of_native_maps core2693 DegreeTwoThreeSpectrum6765.graph DegreeTwoThreeSpectrum5600.graph
    sourceMap2693swap fusedMap2693swap sourceMap2693swap_checked fusedMap2693swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2693
#print axioms sourceMap2693swap_checked
#print axioms fusedMap2693swap_checked
#print axioms certified2693swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
