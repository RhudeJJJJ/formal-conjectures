/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5308 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5308 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,9,6,7,8,1,0,10,11,12,13,14,15] (sourceLabel 4 2 7 v)
def fusedMap5308 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 2 7 v)
theorem sourceMap5308_checked : acceptsGraphIso
    (source (graph core5308) (root 4) 2 7) DegreeTwoThreeSpectrum4059.graph sourceMap5308=true := by decide +kernel
theorem fusedMap5308_checked : acceptsGraphIso
    (fused (graph core5308) (root 4) 2 7) DegreeTwoThreeSpectrum3876.graph fusedMap5308=true := by decide +kernel
theorem certified5308 : Certified (graph core5308) (root 4) 2 7 :=
  of_native_maps core5308 DegreeTwoThreeSpectrum4059.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5308 fusedMap5308 sourceMap5308_checked fusedMap5308_checked
    DegreeTwoThreeFiniteComparisons.comparison5308
#print axioms sourceMap5308_checked
#print axioms fusedMap5308_checked
#print axioms certified5308
def sourceMap5308swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,3,4,5,9,1,0,10,11,12,13,14,15,6,7,8] (sourceLabel 4 7 2 v)
def fusedMap5308swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 7 2 v)
theorem sourceMap5308swap_checked : acceptsGraphIso
    (source (graph core5308) (root 4) 7 2) DegreeTwoThreeSpectrum4059.graph sourceMap5308swap=true := by decide +kernel
theorem fusedMap5308swap_checked : acceptsGraphIso
    (fused (graph core5308) (root 4) 7 2) DegreeTwoThreeSpectrum3876.graph fusedMap5308swap=true := by decide +kernel
theorem certified5308swap : Certified (graph core5308) (root 4) 7 2 :=
  of_native_maps core5308 DegreeTwoThreeSpectrum4059.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5308swap fusedMap5308swap sourceMap5308swap_checked fusedMap5308swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5308
#print axioms sourceMap5308swap_checked
#print axioms fusedMap5308swap_checked
#print axioms certified5308swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
