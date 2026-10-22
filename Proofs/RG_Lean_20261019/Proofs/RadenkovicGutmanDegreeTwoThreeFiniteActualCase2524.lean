/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2524 : Family 10 := level10.get ⟨294,by decide⟩
def sourceMap2524 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2524 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2524_checked : acceptsGraphIso
    (source (graph core2524) (root 10) 0 4) DegreeTwoThreeSpectrum5457.graph sourceMap2524=true := by decide +kernel
theorem fusedMap2524_checked : acceptsGraphIso
    (fused (graph core2524) (root 10) 0 4) DegreeTwoThreeSpectrum5458.graph fusedMap2524=true := by decide +kernel
theorem certified2524 : Certified (graph core2524) (root 10) 0 4 :=
  of_native_maps core2524 DegreeTwoThreeSpectrum5457.graph DegreeTwoThreeSpectrum5458.graph
    sourceMap2524 fusedMap2524 sourceMap2524_checked fusedMap2524_checked
    DegreeTwoThreeFiniteComparisons.comparison2524
#print axioms sourceMap2524_checked
#print axioms fusedMap2524_checked
#print axioms certified2524
def sourceMap2524swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2524swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2524swap_checked : acceptsGraphIso
    (source (graph core2524) (root 10) 4 0) DegreeTwoThreeSpectrum5457.graph sourceMap2524swap=true := by decide +kernel
theorem fusedMap2524swap_checked : acceptsGraphIso
    (fused (graph core2524) (root 10) 4 0) DegreeTwoThreeSpectrum5458.graph fusedMap2524swap=true := by decide +kernel
theorem certified2524swap : Certified (graph core2524) (root 10) 4 0 :=
  of_native_maps core2524 DegreeTwoThreeSpectrum5457.graph DegreeTwoThreeSpectrum5458.graph
    sourceMap2524swap fusedMap2524swap sourceMap2524swap_checked fusedMap2524swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2524
#print axioms sourceMap2524swap_checked
#print axioms fusedMap2524swap_checked
#print axioms certified2524swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
