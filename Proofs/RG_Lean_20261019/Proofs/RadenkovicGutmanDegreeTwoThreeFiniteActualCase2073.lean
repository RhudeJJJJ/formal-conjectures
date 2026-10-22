/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2073 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap2073 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2073 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2073_checked : acceptsGraphIso
    (source (graph core2073) (root 6) 0 4) DegreeOneSmallSpectrum1201.graph sourceMap2073=true := by decide +kernel
theorem fusedMap2073_checked : acceptsGraphIso
    (fused (graph core2073) (root 6) 0 4) DegreeOneSmallSpectrum880.graph fusedMap2073=true := by decide +kernel
theorem certified2073 : Certified (graph core2073) (root 6) 0 4 :=
  of_native_maps core2073 DegreeOneSmallSpectrum1201.graph DegreeOneSmallSpectrum880.graph
    sourceMap2073 fusedMap2073 sourceMap2073_checked fusedMap2073_checked
    DegreeTwoThreeFiniteComparisons.comparison2073
#print axioms sourceMap2073_checked
#print axioms fusedMap2073_checked
#print axioms certified2073
def sourceMap2073swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2073swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2073swap_checked : acceptsGraphIso
    (source (graph core2073) (root 6) 4 0) DegreeOneSmallSpectrum1201.graph sourceMap2073swap=true := by decide +kernel
theorem fusedMap2073swap_checked : acceptsGraphIso
    (fused (graph core2073) (root 6) 4 0) DegreeOneSmallSpectrum880.graph fusedMap2073swap=true := by decide +kernel
theorem certified2073swap : Certified (graph core2073) (root 6) 4 0 :=
  of_native_maps core2073 DegreeOneSmallSpectrum1201.graph DegreeOneSmallSpectrum880.graph
    sourceMap2073swap fusedMap2073swap sourceMap2073swap_checked fusedMap2073swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2073
#print axioms sourceMap2073swap_checked
#print axioms fusedMap2073swap_checked
#print axioms certified2073swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
