/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5098 : Family 7 := level7.get ⟨56,by decide⟩
def sourceMap5098 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5098 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5098_checked : acceptsGraphIso
    (source (graph core5098) (root 7) 2 4) DegreeTwoThreeSpectrum4613.graph sourceMap5098=true := by decide +kernel
theorem fusedMap5098_checked : acceptsGraphIso
    (fused (graph core5098) (root 7) 2 4) DegreeTwoThreeSpectrum4096.graph fusedMap5098=true := by decide +kernel
theorem certified5098 : Certified (graph core5098) (root 7) 2 4 :=
  of_native_maps core5098 DegreeTwoThreeSpectrum4613.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap5098 fusedMap5098 sourceMap5098_checked fusedMap5098_checked
    DegreeTwoThreeFiniteComparisons.comparison5098
#print axioms sourceMap5098_checked
#print axioms fusedMap5098_checked
#print axioms certified5098
def sourceMap5098swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5098swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5098swap_checked : acceptsGraphIso
    (source (graph core5098) (root 7) 4 2) DegreeTwoThreeSpectrum4613.graph sourceMap5098swap=true := by decide +kernel
theorem fusedMap5098swap_checked : acceptsGraphIso
    (fused (graph core5098) (root 7) 4 2) DegreeTwoThreeSpectrum4096.graph fusedMap5098swap=true := by decide +kernel
theorem certified5098swap : Certified (graph core5098) (root 7) 4 2 :=
  of_native_maps core5098 DegreeTwoThreeSpectrum4613.graph DegreeTwoThreeSpectrum4096.graph
    sourceMap5098swap fusedMap5098swap sourceMap5098swap_checked fusedMap5098swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5098
#print axioms sourceMap5098swap_checked
#print axioms fusedMap5098swap_checked
#print axioms certified5098swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
