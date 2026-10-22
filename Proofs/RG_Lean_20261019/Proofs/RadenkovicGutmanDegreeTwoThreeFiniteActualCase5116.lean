/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5116 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap5116 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5116 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5116_checked : acceptsGraphIso
    (source (graph core5116) (root 7) 2 4) DegreeTwoThreeSpectrum4900.graph sourceMap5116=true := by decide +kernel
theorem fusedMap5116_checked : acceptsGraphIso
    (fused (graph core5116) (root 7) 2 4) DegreeTwoThreeSpectrum4176.graph fusedMap5116=true := by decide +kernel
theorem certified5116 : Certified (graph core5116) (root 7) 2 4 :=
  of_native_maps core5116 DegreeTwoThreeSpectrum4900.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap5116 fusedMap5116 sourceMap5116_checked fusedMap5116_checked
    DegreeTwoThreeFiniteComparisons.comparison5116
#print axioms sourceMap5116_checked
#print axioms fusedMap5116_checked
#print axioms certified5116
def sourceMap5116swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,2,3,4] (sourceLabel 7 4 2 v)
def fusedMap5116swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5116swap_checked : acceptsGraphIso
    (source (graph core5116) (root 7) 4 2) DegreeTwoThreeSpectrum4900.graph sourceMap5116swap=true := by decide +kernel
theorem fusedMap5116swap_checked : acceptsGraphIso
    (fused (graph core5116) (root 7) 4 2) DegreeTwoThreeSpectrum4176.graph fusedMap5116swap=true := by decide +kernel
theorem certified5116swap : Certified (graph core5116) (root 7) 4 2 :=
  of_native_maps core5116 DegreeTwoThreeSpectrum4900.graph DegreeTwoThreeSpectrum4176.graph
    sourceMap5116swap fusedMap5116swap sourceMap5116swap_checked fusedMap5116swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5116
#print axioms sourceMap5116swap_checked
#print axioms fusedMap5116swap_checked
#print axioms certified5116swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
