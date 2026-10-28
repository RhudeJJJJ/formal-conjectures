/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5240 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap5240 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5240 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5240_checked : acceptsGraphIso
    (source (graph core5240) (root 6) 2 5) DegreeTwoThreeSpectrum4565.graph sourceMap5240=true := by decide +kernel
theorem fusedMap5240_checked : acceptsGraphIso
    (fused (graph core5240) (root 6) 2 5) DegreeTwoThreeSpectrum3897.graph fusedMap5240=true := by decide +kernel
theorem certified5240 : Certified (graph core5240) (root 6) 2 5 :=
  of_native_maps core5240 DegreeTwoThreeSpectrum4565.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap5240 fusedMap5240 sourceMap5240_checked fusedMap5240_checked
    DegreeTwoThreeFiniteComparisons.comparison5240
#print axioms sourceMap5240_checked
#print axioms fusedMap5240_checked
#print axioms certified5240
def sourceMap5240swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,15,2,3,4] (sourceLabel 6 5 2 v)
def fusedMap5240swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5240swap_checked : acceptsGraphIso
    (source (graph core5240) (root 6) 5 2) DegreeTwoThreeSpectrum4565.graph sourceMap5240swap=true := by decide +kernel
theorem fusedMap5240swap_checked : acceptsGraphIso
    (fused (graph core5240) (root 6) 5 2) DegreeTwoThreeSpectrum3897.graph fusedMap5240swap=true := by decide +kernel
theorem certified5240swap : Certified (graph core5240) (root 6) 5 2 :=
  of_native_maps core5240 DegreeTwoThreeSpectrum4565.graph DegreeTwoThreeSpectrum3897.graph
    sourceMap5240swap fusedMap5240swap sourceMap5240swap_checked fusedMap5240swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5240
#print axioms sourceMap5240swap_checked
#print axioms fusedMap5240swap_checked
#print axioms certified5240swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
