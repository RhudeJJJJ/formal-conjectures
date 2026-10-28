/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5309 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5309 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,6,7,8,9,3,4,5,1,0,10,11,12,13,14,15] (sourceLabel 4 2 7 v)
def fusedMap5309 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 2 7 v)
theorem sourceMap5309_checked : acceptsGraphIso
    (source (graph core5309) (root 4) 2 7) DegreeTwoThreeSpectrum4064.graph sourceMap5309=true := by decide +kernel
theorem fusedMap5309_checked : acceptsGraphIso
    (fused (graph core5309) (root 4) 2 7) DegreeTwoThreeSpectrum3855.graph fusedMap5309=true := by decide +kernel
theorem certified5309 : Certified (graph core5309) (root 4) 2 7 :=
  of_native_maps core5309 DegreeTwoThreeSpectrum4064.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5309 fusedMap5309 sourceMap5309_checked fusedMap5309_checked
    DegreeTwoThreeFiniteComparisons.comparison5309
#print axioms sourceMap5309_checked
#print axioms fusedMap5309_checked
#print axioms certified5309
def sourceMap5309swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,6,7,8,9,1,0,10,11,12,13,14,15,3,4,5] (sourceLabel 4 7 2 v)
def fusedMap5309swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 7 2 v)
theorem sourceMap5309swap_checked : acceptsGraphIso
    (source (graph core5309) (root 4) 7 2) DegreeTwoThreeSpectrum4064.graph sourceMap5309swap=true := by decide +kernel
theorem fusedMap5309swap_checked : acceptsGraphIso
    (fused (graph core5309) (root 4) 7 2) DegreeTwoThreeSpectrum3855.graph fusedMap5309swap=true := by decide +kernel
theorem certified5309swap : Certified (graph core5309) (root 4) 7 2 :=
  of_native_maps core5309 DegreeTwoThreeSpectrum4064.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5309swap fusedMap5309swap sourceMap5309swap_checked fusedMap5309swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5309
#print axioms sourceMap5309swap_checked
#print axioms fusedMap5309swap_checked
#print axioms certified5309swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
