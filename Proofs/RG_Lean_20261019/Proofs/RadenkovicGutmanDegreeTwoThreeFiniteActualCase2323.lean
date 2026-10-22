/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2323 : Family 9 := level9.get ⟨356,by decide⟩
def sourceMap2323 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2323 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2323_checked : acceptsGraphIso
    (source (graph core2323) (root 9) 0 4) DegreeTwoThreeSpectrum4265.graph sourceMap2323=true := by decide +kernel
theorem fusedMap2323_checked : acceptsGraphIso
    (fused (graph core2323) (root 9) 0 4) DegreeTwoThreeSpectrum4266.graph fusedMap2323=true := by decide +kernel
theorem certified2323 : Certified (graph core2323) (root 9) 0 4 :=
  of_native_maps core2323 DegreeTwoThreeSpectrum4265.graph DegreeTwoThreeSpectrum4266.graph
    sourceMap2323 fusedMap2323 sourceMap2323_checked fusedMap2323_checked
    DegreeTwoThreeFiniteComparisons.comparison2323
#print axioms sourceMap2323_checked
#print axioms fusedMap2323_checked
#print axioms certified2323
def sourceMap2323swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2323swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2323swap_checked : acceptsGraphIso
    (source (graph core2323) (root 9) 4 0) DegreeTwoThreeSpectrum4265.graph sourceMap2323swap=true := by decide +kernel
theorem fusedMap2323swap_checked : acceptsGraphIso
    (fused (graph core2323) (root 9) 4 0) DegreeTwoThreeSpectrum4266.graph fusedMap2323swap=true := by decide +kernel
theorem certified2323swap : Certified (graph core2323) (root 9) 4 0 :=
  of_native_maps core2323 DegreeTwoThreeSpectrum4265.graph DegreeTwoThreeSpectrum4266.graph
    sourceMap2323swap fusedMap2323swap sourceMap2323swap_checked fusedMap2323swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2323
#print axioms sourceMap2323swap_checked
#print axioms fusedMap2323swap_checked
#print axioms certified2323swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
