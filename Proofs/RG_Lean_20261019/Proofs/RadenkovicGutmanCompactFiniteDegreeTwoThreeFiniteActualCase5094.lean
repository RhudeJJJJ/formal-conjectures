/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5094 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap5094 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5094 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5094_checked : acceptsGraphIso
    (source (graph core5094) (root 7) 2 4) DegreeTwoThreeSpectrum4507.graph sourceMap5094=true := by decide +kernel
theorem fusedMap5094_checked : acceptsGraphIso
    (fused (graph core5094) (root 7) 2 4) DegreeTwoThreeSpectrum4030.graph fusedMap5094=true := by decide +kernel
theorem certified5094 : Certified (graph core5094) (root 7) 2 4 :=
  of_native_maps core5094 DegreeTwoThreeSpectrum4507.graph DegreeTwoThreeSpectrum4030.graph
    sourceMap5094 fusedMap5094 sourceMap5094_checked fusedMap5094_checked
    DegreeTwoThreeFiniteComparisons.comparison5094
#print axioms sourceMap5094_checked
#print axioms fusedMap5094_checked
#print axioms certified5094
def sourceMap5094swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5094swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5094swap_checked : acceptsGraphIso
    (source (graph core5094) (root 7) 4 2) DegreeTwoThreeSpectrum4507.graph sourceMap5094swap=true := by decide +kernel
theorem fusedMap5094swap_checked : acceptsGraphIso
    (fused (graph core5094) (root 7) 4 2) DegreeTwoThreeSpectrum4030.graph fusedMap5094swap=true := by decide +kernel
theorem certified5094swap : Certified (graph core5094) (root 7) 4 2 :=
  of_native_maps core5094 DegreeTwoThreeSpectrum4507.graph DegreeTwoThreeSpectrum4030.graph
    sourceMap5094swap fusedMap5094swap sourceMap5094swap_checked fusedMap5094swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5094
#print axioms sourceMap5094swap_checked
#print axioms fusedMap5094swap_checked
#print axioms certified5094swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
