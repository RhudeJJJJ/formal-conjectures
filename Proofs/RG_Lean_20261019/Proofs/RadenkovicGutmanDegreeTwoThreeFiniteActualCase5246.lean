/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5246 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap5246 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5246 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5246_checked : acceptsGraphIso
    (source (graph core5246) (root 7) 2 5) DegreeTwoThreeSpectrum5888.graph sourceMap5246=true := by decide +kernel
theorem fusedMap5246_checked : acceptsGraphIso
    (fused (graph core5246) (root 7) 2 5) DegreeTwoThreeSpectrum5096.graph fusedMap5246=true := by decide +kernel
theorem certified5246 : Certified (graph core5246) (root 7) 2 5 :=
  of_native_maps core5246 DegreeTwoThreeSpectrum5888.graph DegreeTwoThreeSpectrum5096.graph
    sourceMap5246 fusedMap5246 sourceMap5246_checked fusedMap5246_checked
    DegreeTwoThreeFiniteComparisons.comparison5246
#print axioms sourceMap5246_checked
#print axioms fusedMap5246_checked
#print axioms certified5246
def sourceMap5246swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5246swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5246swap_checked : acceptsGraphIso
    (source (graph core5246) (root 7) 5 2) DegreeTwoThreeSpectrum5888.graph sourceMap5246swap=true := by decide +kernel
theorem fusedMap5246swap_checked : acceptsGraphIso
    (fused (graph core5246) (root 7) 5 2) DegreeTwoThreeSpectrum5096.graph fusedMap5246swap=true := by decide +kernel
theorem certified5246swap : Certified (graph core5246) (root 7) 5 2 :=
  of_native_maps core5246 DegreeTwoThreeSpectrum5888.graph DegreeTwoThreeSpectrum5096.graph
    sourceMap5246swap fusedMap5246swap sourceMap5246swap_checked fusedMap5246swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5246
#print axioms sourceMap5246swap_checked
#print axioms fusedMap5246swap_checked
#print axioms certified5246swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
