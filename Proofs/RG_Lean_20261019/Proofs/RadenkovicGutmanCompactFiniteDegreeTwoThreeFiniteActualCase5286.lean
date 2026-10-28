/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5286 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5286 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,10,7,8,9,1,0,11,12,13,14,15] (sourceLabel 5 2 6 v)
def fusedMap5286 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 2 6 v)
theorem sourceMap5286_checked : acceptsGraphIso
    (source (graph core5286) (root 5) 2 6) DegreeTwoThreeSpectrum4484.graph sourceMap5286=true := by decide +kernel
theorem fusedMap5286_checked : acceptsGraphIso
    (fused (graph core5286) (root 5) 2 6) DegreeTwoThreeSpectrum3864.graph fusedMap5286=true := by decide +kernel
theorem certified5286 : Certified (graph core5286) (root 5) 2 6 :=
  of_native_maps core5286 DegreeTwoThreeSpectrum4484.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap5286 fusedMap5286 sourceMap5286_checked fusedMap5286_checked
    DegreeTwoThreeFiniteComparisons.comparison5286
#print axioms sourceMap5286_checked
#print axioms fusedMap5286_checked
#print axioms certified5286
def sourceMap5286swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,3,4,5,6,10,1,0,11,12,13,14,15,7,8,9] (sourceLabel 5 6 2 v)
def fusedMap5286swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 6 2 v)
theorem sourceMap5286swap_checked : acceptsGraphIso
    (source (graph core5286) (root 5) 6 2) DegreeTwoThreeSpectrum4484.graph sourceMap5286swap=true := by decide +kernel
theorem fusedMap5286swap_checked : acceptsGraphIso
    (fused (graph core5286) (root 5) 6 2) DegreeTwoThreeSpectrum3864.graph fusedMap5286swap=true := by decide +kernel
theorem certified5286swap : Certified (graph core5286) (root 5) 6 2 :=
  of_native_maps core5286 DegreeTwoThreeSpectrum4484.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap5286swap fusedMap5286swap sourceMap5286swap_checked fusedMap5286swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5286
#print axioms sourceMap5286swap_checked
#print axioms fusedMap5286swap_checked
#print axioms certified5286swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
