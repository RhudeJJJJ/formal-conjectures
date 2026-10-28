/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5316 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5316 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,3,4,5,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5316 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5316_checked : acceptsGraphIso
    (source (graph core5316) (root 5) 2 7) DegreeTwoThreeSpectrum5676.graph sourceMap5316=true := by decide +kernel
theorem fusedMap5316_checked : acceptsGraphIso
    (fused (graph core5316) (root 5) 2 7) DegreeTwoThreeSpectrum4973.graph fusedMap5316=true := by decide +kernel
theorem certified5316 : Certified (graph core5316) (root 5) 2 7 :=
  of_native_maps core5316 DegreeTwoThreeSpectrum5676.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap5316 fusedMap5316 sourceMap5316_checked fusedMap5316_checked
    DegreeTwoThreeFiniteComparisons.comparison5316
#print axioms sourceMap5316_checked
#print axioms fusedMap5316_checked
#print axioms certified5316
def sourceMap5316swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,6,7,8,9,10,1,0,11,12,13,14,15,16,3,4,5] (sourceLabel 5 7 2 v)
def fusedMap5316swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5316swap_checked : acceptsGraphIso
    (source (graph core5316) (root 5) 7 2) DegreeTwoThreeSpectrum5676.graph sourceMap5316swap=true := by decide +kernel
theorem fusedMap5316swap_checked : acceptsGraphIso
    (fused (graph core5316) (root 5) 7 2) DegreeTwoThreeSpectrum4973.graph fusedMap5316swap=true := by decide +kernel
theorem certified5316swap : Certified (graph core5316) (root 5) 7 2 :=
  of_native_maps core5316 DegreeTwoThreeSpectrum5676.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap5316swap fusedMap5316swap sourceMap5316swap_checked fusedMap5316swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5316
#print axioms sourceMap5316swap_checked
#print axioms fusedMap5316swap_checked
#print axioms certified5316swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
