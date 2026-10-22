/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5238 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap5238 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,8,9,10,5,6,7,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5238 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5238_checked : acceptsGraphIso
    (source (graph core5238) (root 6) 2 5) DegreeTwoThreeSpectrum4540.graph sourceMap5238=true := by decide +kernel
theorem fusedMap5238_checked : acceptsGraphIso
    (fused (graph core5238) (root 6) 2 5) DegreeTwoThreeSpectrum4067.graph fusedMap5238=true := by decide +kernel
theorem certified5238 : Certified (graph core5238) (root 6) 2 5 :=
  of_native_maps core5238 DegreeTwoThreeSpectrum4540.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap5238 fusedMap5238 sourceMap5238_checked fusedMap5238_checked
    DegreeTwoThreeFiniteComparisons.comparison5238
#print axioms sourceMap5238_checked
#print axioms fusedMap5238_checked
#print axioms certified5238
def sourceMap5238swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,8,9,10,0,11,12,13,14,15,5,6,7] (sourceLabel 6 5 2 v)
def fusedMap5238swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5238swap_checked : acceptsGraphIso
    (source (graph core5238) (root 6) 5 2) DegreeTwoThreeSpectrum4540.graph sourceMap5238swap=true := by decide +kernel
theorem fusedMap5238swap_checked : acceptsGraphIso
    (fused (graph core5238) (root 6) 5 2) DegreeTwoThreeSpectrum4067.graph fusedMap5238swap=true := by decide +kernel
theorem certified5238swap : Certified (graph core5238) (root 6) 5 2 :=
  of_native_maps core5238 DegreeTwoThreeSpectrum4540.graph DegreeTwoThreeSpectrum4067.graph
    sourceMap5238swap fusedMap5238swap sourceMap5238swap_checked fusedMap5238swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5238
#print axioms sourceMap5238swap_checked
#print axioms fusedMap5238swap_checked
#print axioms certified5238swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
