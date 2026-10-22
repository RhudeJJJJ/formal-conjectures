/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2551 : Family 10 := level10.get ⟨387,by decide⟩
def sourceMap2551 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2551 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2551_checked : acceptsGraphIso
    (source (graph core2551) (root 10) 0 4) DegreeTwoThreeSpectrum5720.graph sourceMap2551=true := by decide +kernel
theorem fusedMap2551_checked : acceptsGraphIso
    (fused (graph core2551) (root 10) 0 4) DegreeTwoThreeSpectrum5721.graph fusedMap2551=true := by decide +kernel
theorem certified2551 : Certified (graph core2551) (root 10) 0 4 :=
  of_native_maps core2551 DegreeTwoThreeSpectrum5720.graph DegreeTwoThreeSpectrum5721.graph
    sourceMap2551 fusedMap2551 sourceMap2551_checked fusedMap2551_checked
    DegreeTwoThreeFiniteComparisons.comparison2551
#print axioms sourceMap2551_checked
#print axioms fusedMap2551_checked
#print axioms certified2551
def sourceMap2551swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2551swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2551swap_checked : acceptsGraphIso
    (source (graph core2551) (root 10) 4 0) DegreeTwoThreeSpectrum5720.graph sourceMap2551swap=true := by decide +kernel
theorem fusedMap2551swap_checked : acceptsGraphIso
    (fused (graph core2551) (root 10) 4 0) DegreeTwoThreeSpectrum5721.graph fusedMap2551swap=true := by decide +kernel
theorem certified2551swap : Certified (graph core2551) (root 10) 4 0 :=
  of_native_maps core2551 DegreeTwoThreeSpectrum5720.graph DegreeTwoThreeSpectrum5721.graph
    sourceMap2551swap fusedMap2551swap sourceMap2551swap_checked fusedMap2551swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2551
#print axioms sourceMap2551swap_checked
#print axioms fusedMap2551swap_checked
#print axioms certified2551swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
