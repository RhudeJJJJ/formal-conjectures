/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2484 : Family 10 := level10.get ⟨154,by decide⟩
def sourceMap2484 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2484 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2484_checked : acceptsGraphIso
    (source (graph core2484) (root 10) 0 4) DegreeTwoThreeSpectrum5882.graph sourceMap2484=true := by decide +kernel
theorem fusedMap2484_checked : acceptsGraphIso
    (fused (graph core2484) (root 10) 0 4) DegreeTwoThreeSpectrum5090.graph fusedMap2484=true := by decide +kernel
theorem certified2484 : Certified (graph core2484) (root 10) 0 4 :=
  of_native_maps core2484 DegreeTwoThreeSpectrum5882.graph DegreeTwoThreeSpectrum5090.graph
    sourceMap2484 fusedMap2484 sourceMap2484_checked fusedMap2484_checked
    DegreeTwoThreeFiniteComparisons.comparison2484
#print axioms sourceMap2484_checked
#print axioms fusedMap2484_checked
#print axioms certified2484
def sourceMap2484swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2484swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2484swap_checked : acceptsGraphIso
    (source (graph core2484) (root 10) 4 0) DegreeTwoThreeSpectrum5882.graph sourceMap2484swap=true := by decide +kernel
theorem fusedMap2484swap_checked : acceptsGraphIso
    (fused (graph core2484) (root 10) 4 0) DegreeTwoThreeSpectrum5090.graph fusedMap2484swap=true := by decide +kernel
theorem certified2484swap : Certified (graph core2484) (root 10) 4 0 :=
  of_native_maps core2484 DegreeTwoThreeSpectrum5882.graph DegreeTwoThreeSpectrum5090.graph
    sourceMap2484swap fusedMap2484swap sourceMap2484swap_checked fusedMap2484swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2484
#print axioms sourceMap2484swap_checked
#print axioms fusedMap2484swap_checked
#print axioms certified2484swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
