/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2482 : Family 10 := level10.get ⟨143,by decide⟩
def sourceMap2482 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2482 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2482_checked : acceptsGraphIso
    (source (graph core2482) (root 10) 0 4) DegreeTwoThreeSpectrum5813.graph sourceMap2482=true := by decide +kernel
theorem fusedMap2482_checked : acceptsGraphIso
    (fused (graph core2482) (root 10) 0 4) DegreeTwoThreeSpectrum5077.graph fusedMap2482=true := by decide +kernel
theorem certified2482 : Certified (graph core2482) (root 10) 0 4 :=
  of_native_maps core2482 DegreeTwoThreeSpectrum5813.graph DegreeTwoThreeSpectrum5077.graph
    sourceMap2482 fusedMap2482 sourceMap2482_checked fusedMap2482_checked
    DegreeTwoThreeFiniteComparisons.comparison2482
#print axioms sourceMap2482_checked
#print axioms fusedMap2482_checked
#print axioms certified2482
def sourceMap2482swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2482swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2482swap_checked : acceptsGraphIso
    (source (graph core2482) (root 10) 4 0) DegreeTwoThreeSpectrum5813.graph sourceMap2482swap=true := by decide +kernel
theorem fusedMap2482swap_checked : acceptsGraphIso
    (fused (graph core2482) (root 10) 4 0) DegreeTwoThreeSpectrum5077.graph fusedMap2482swap=true := by decide +kernel
theorem certified2482swap : Certified (graph core2482) (root 10) 4 0 :=
  of_native_maps core2482 DegreeTwoThreeSpectrum5813.graph DegreeTwoThreeSpectrum5077.graph
    sourceMap2482swap fusedMap2482swap sourceMap2482swap_checked fusedMap2482swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2482
#print axioms sourceMap2482swap_checked
#print axioms fusedMap2482swap_checked
#print axioms certified2482swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
