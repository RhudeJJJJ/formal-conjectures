/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5321 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5321 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,7,8,9,10,4,5,6,2,1,0,11,12,13,14,15,16] (sourceLabel 4 2 8 v)
def fusedMap5321 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 2 8 v)
theorem sourceMap5321_checked : acceptsGraphIso
    (source (graph core5321) (root 4) 2 8) DegreeTwoThreeSpectrum5691.graph sourceMap5321=true := by decide +kernel
theorem fusedMap5321_checked : acceptsGraphIso
    (fused (graph core5321) (root 4) 2 8) DegreeTwoThreeSpectrum5014.graph fusedMap5321=true := by decide +kernel
theorem certified5321 : Certified (graph core5321) (root 4) 2 8 :=
  of_native_maps core5321 DegreeTwoThreeSpectrum5691.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap5321 fusedMap5321 sourceMap5321_checked fusedMap5321_checked
    DegreeTwoThreeFiniteComparisons.comparison5321
#print axioms sourceMap5321_checked
#print axioms fusedMap5321_checked
#print axioms certified5321
def sourceMap5321swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,7,8,9,10,2,1,0,11,12,13,14,15,16,4,5,6] (sourceLabel 4 8 2 v)
def fusedMap5321swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 8 2 v)
theorem sourceMap5321swap_checked : acceptsGraphIso
    (source (graph core5321) (root 4) 8 2) DegreeTwoThreeSpectrum5691.graph sourceMap5321swap=true := by decide +kernel
theorem fusedMap5321swap_checked : acceptsGraphIso
    (fused (graph core5321) (root 4) 8 2) DegreeTwoThreeSpectrum5014.graph fusedMap5321swap=true := by decide +kernel
theorem certified5321swap : Certified (graph core5321) (root 4) 8 2 :=
  of_native_maps core5321 DegreeTwoThreeSpectrum5691.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap5321swap fusedMap5321swap sourceMap5321swap_checked fusedMap5321swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5321
#print axioms sourceMap5321swap_checked
#print axioms fusedMap5321swap_checked
#print axioms certified5321swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
