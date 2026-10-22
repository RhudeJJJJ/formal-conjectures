/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2047 : Family 10 := level10.get ⟨1785,by decide⟩
def sourceMap2047 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,7,8,9,10,11,12,13,14,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap2047 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2047_checked : acceptsGraphIso
    (source (graph core2047) (root 10) 0 2) DegreeTwoThreeSpectrum3850.graph sourceMap2047=true := by decide +kernel
theorem fusedMap2047_checked : acceptsGraphIso
    (fused (graph core2047) (root 10) 0 2) DegreeTwoThreeSpectrum3635.graph fusedMap2047=true := by decide +kernel
theorem certified2047 : Certified (graph core2047) (root 10) 0 2 :=
  of_native_maps core2047 DegreeTwoThreeSpectrum3850.graph DegreeTwoThreeSpectrum3635.graph
    sourceMap2047 fusedMap2047 sourceMap2047_checked fusedMap2047_checked
    DegreeTwoThreeFiniteComparisons.comparison2047
#print axioms sourceMap2047_checked
#print axioms fusedMap2047_checked
#print axioms certified2047
def sourceMap2047swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,7,8,9,10,11,12,13,4,5,6,14] (sourceLabel 10 2 0 v)
def fusedMap2047swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2047swap_checked : acceptsGraphIso
    (source (graph core2047) (root 10) 2 0) DegreeTwoThreeSpectrum3850.graph sourceMap2047swap=true := by decide +kernel
theorem fusedMap2047swap_checked : acceptsGraphIso
    (fused (graph core2047) (root 10) 2 0) DegreeTwoThreeSpectrum3635.graph fusedMap2047swap=true := by decide +kernel
theorem certified2047swap : Certified (graph core2047) (root 10) 2 0 :=
  of_native_maps core2047 DegreeTwoThreeSpectrum3850.graph DegreeTwoThreeSpectrum3635.graph
    sourceMap2047swap fusedMap2047swap sourceMap2047swap_checked fusedMap2047swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2047
#print axioms sourceMap2047swap_checked
#print axioms fusedMap2047swap_checked
#print axioms certified2047swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
