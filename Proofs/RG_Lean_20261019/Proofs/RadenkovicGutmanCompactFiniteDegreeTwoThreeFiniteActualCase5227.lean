/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5227 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap5227 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5227 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5227_checked : acceptsGraphIso
    (source (graph core5227) (root 6) 2 5) DegreeTwoThreeSpectrum4375.graph sourceMap5227=true := by decide +kernel
theorem fusedMap5227_checked : acceptsGraphIso
    (fused (graph core5227) (root 6) 2 5) DegreeTwoThreeSpectrum3857.graph fusedMap5227=true := by decide +kernel
theorem certified5227 : Certified (graph core5227) (root 6) 2 5 :=
  of_native_maps core5227 DegreeTwoThreeSpectrum4375.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap5227 fusedMap5227 sourceMap5227_checked fusedMap5227_checked
    DegreeTwoThreeFiniteComparisons.comparison5227
#print axioms sourceMap5227_checked
#print axioms fusedMap5227_checked
#print axioms certified5227
def sourceMap5227swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5227swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5227swap_checked : acceptsGraphIso
    (source (graph core5227) (root 6) 5 2) DegreeTwoThreeSpectrum4375.graph sourceMap5227swap=true := by decide +kernel
theorem fusedMap5227swap_checked : acceptsGraphIso
    (fused (graph core5227) (root 6) 5 2) DegreeTwoThreeSpectrum3857.graph fusedMap5227swap=true := by decide +kernel
theorem certified5227swap : Certified (graph core5227) (root 6) 5 2 :=
  of_native_maps core5227 DegreeTwoThreeSpectrum4375.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap5227swap fusedMap5227swap sourceMap5227swap_checked fusedMap5227swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5227
#print axioms sourceMap5227swap_checked
#print axioms fusedMap5227swap_checked
#print axioms certified5227swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
