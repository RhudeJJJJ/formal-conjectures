/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2722 : Family 10 := level10.get ⟨880,by decide⟩
def sourceMap2722 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2722 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2722_checked : acceptsGraphIso
    (source (graph core2722) (root 10) 0 4) DegreeTwoThreeSpectrum6942.graph sourceMap2722=true := by decide +kernel
theorem fusedMap2722_checked : acceptsGraphIso
    (fused (graph core2722) (root 10) 0 4) DegreeTwoThreeSpectrum5730.graph fusedMap2722=true := by decide +kernel
theorem certified2722 : Certified (graph core2722) (root 10) 0 4 :=
  of_native_maps core2722 DegreeTwoThreeSpectrum6942.graph DegreeTwoThreeSpectrum5730.graph
    sourceMap2722 fusedMap2722 sourceMap2722_checked fusedMap2722_checked
    DegreeTwoThreeFiniteComparisons.comparison2722
#print axioms sourceMap2722_checked
#print axioms fusedMap2722_checked
#print axioms certified2722
def sourceMap2722swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2722swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2722swap_checked : acceptsGraphIso
    (source (graph core2722) (root 10) 4 0) DegreeTwoThreeSpectrum6942.graph sourceMap2722swap=true := by decide +kernel
theorem fusedMap2722swap_checked : acceptsGraphIso
    (fused (graph core2722) (root 10) 4 0) DegreeTwoThreeSpectrum5730.graph fusedMap2722swap=true := by decide +kernel
theorem certified2722swap : Certified (graph core2722) (root 10) 4 0 :=
  of_native_maps core2722 DegreeTwoThreeSpectrum6942.graph DegreeTwoThreeSpectrum5730.graph
    sourceMap2722swap fusedMap2722swap sourceMap2722swap_checked fusedMap2722swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2722
#print axioms sourceMap2722swap_checked
#print axioms fusedMap2722swap_checked
#print axioms certified2722swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
