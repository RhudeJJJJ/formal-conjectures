/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2308 : Family 9 := level9.get ⟨310,by decide⟩
def sourceMap2308 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 9 0 4 v)
def fusedMap2308 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2308_checked : acceptsGraphIso
    (source (graph core2308) (root 9) 0 4) DegreeTwoThreeSpectrum4660.graph sourceMap2308=true := by decide +kernel
theorem fusedMap2308_checked : acceptsGraphIso
    (fused (graph core2308) (root 9) 0 4) DegreeTwoThreeSpectrum4152.graph fusedMap2308=true := by decide +kernel
theorem certified2308 : Certified (graph core2308) (root 9) 0 4 :=
  of_native_maps core2308 DegreeTwoThreeSpectrum4660.graph DegreeTwoThreeSpectrum4152.graph
    sourceMap2308 fusedMap2308 sourceMap2308_checked fusedMap2308_checked
    DegreeTwoThreeFiniteComparisons.comparison2308
#print axioms sourceMap2308_checked
#print axioms fusedMap2308_checked
#print axioms certified2308
def sourceMap2308swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10,15] (sourceLabel 9 4 0 v)
def fusedMap2308swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2308swap_checked : acceptsGraphIso
    (source (graph core2308) (root 9) 4 0) DegreeTwoThreeSpectrum4660.graph sourceMap2308swap=true := by decide +kernel
theorem fusedMap2308swap_checked : acceptsGraphIso
    (fused (graph core2308) (root 9) 4 0) DegreeTwoThreeSpectrum4152.graph fusedMap2308swap=true := by decide +kernel
theorem certified2308swap : Certified (graph core2308) (root 9) 4 0 :=
  of_native_maps core2308 DegreeTwoThreeSpectrum4660.graph DegreeTwoThreeSpectrum4152.graph
    sourceMap2308swap fusedMap2308swap sourceMap2308swap_checked fusedMap2308swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2308
#print axioms sourceMap2308swap_checked
#print axioms fusedMap2308swap_checked
#print axioms certified2308swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
