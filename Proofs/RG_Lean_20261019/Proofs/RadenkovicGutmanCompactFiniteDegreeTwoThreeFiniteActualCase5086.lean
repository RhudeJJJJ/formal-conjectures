/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5086 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap5086 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,12,13,14,7,8,9,10,11] (sourceLabel 7 2 4 v)
def fusedMap5086 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5086_checked : acceptsGraphIso
    (source (graph core5086) (root 7) 2 4) DegreeTwoThreeSpectrum4655.graph sourceMap5086=true := by decide +kernel
theorem fusedMap5086_checked : acceptsGraphIso
    (fused (graph core5086) (root 7) 2 4) DegreeTwoThreeSpectrum3879.graph fusedMap5086=true := by decide +kernel
theorem certified5086 : Certified (graph core5086) (root 7) 2 4 :=
  of_native_maps core5086 DegreeTwoThreeSpectrum4655.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap5086 fusedMap5086 sourceMap5086_checked fusedMap5086_checked
    DegreeTwoThreeFiniteComparisons.comparison5086
#print axioms sourceMap5086_checked
#print axioms fusedMap5086_checked
#print axioms certified5086
def sourceMap5086swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,7,8,9,10,11,12,13,14] (sourceLabel 7 4 2 v)
def fusedMap5086swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5086swap_checked : acceptsGraphIso
    (source (graph core5086) (root 7) 4 2) DegreeTwoThreeSpectrum4655.graph sourceMap5086swap=true := by decide +kernel
theorem fusedMap5086swap_checked : acceptsGraphIso
    (fused (graph core5086) (root 7) 4 2) DegreeTwoThreeSpectrum3879.graph fusedMap5086swap=true := by decide +kernel
theorem certified5086swap : Certified (graph core5086) (root 7) 4 2 :=
  of_native_maps core5086 DegreeTwoThreeSpectrum4655.graph DegreeTwoThreeSpectrum3879.graph
    sourceMap5086swap fusedMap5086swap sourceMap5086swap_checked fusedMap5086swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5086
#print axioms sourceMap5086swap_checked
#print axioms fusedMap5086swap_checked
#print axioms certified5086swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
