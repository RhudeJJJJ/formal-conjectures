/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2466 : Family 10 := level10.get ⟨77,by decide⟩
def sourceMap2466 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2466 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2466_checked : acceptsGraphIso
    (source (graph core2466) (root 10) 0 4) DegreeTwoThreeSpectrum5393.graph sourceMap2466=true := by decide +kernel
theorem fusedMap2466_checked : acceptsGraphIso
    (fused (graph core2466) (root 10) 0 4) DegreeTwoThreeSpectrum4992.graph fusedMap2466=true := by decide +kernel
theorem certified2466 : Certified (graph core2466) (root 10) 0 4 :=
  of_native_maps core2466 DegreeTwoThreeSpectrum5393.graph DegreeTwoThreeSpectrum4992.graph
    sourceMap2466 fusedMap2466 sourceMap2466_checked fusedMap2466_checked
    DegreeTwoThreeFiniteComparisons.comparison2466
#print axioms sourceMap2466_checked
#print axioms fusedMap2466_checked
#print axioms certified2466
def sourceMap2466swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2466swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2466swap_checked : acceptsGraphIso
    (source (graph core2466) (root 10) 4 0) DegreeTwoThreeSpectrum5393.graph sourceMap2466swap=true := by decide +kernel
theorem fusedMap2466swap_checked : acceptsGraphIso
    (fused (graph core2466) (root 10) 4 0) DegreeTwoThreeSpectrum4992.graph fusedMap2466swap=true := by decide +kernel
theorem certified2466swap : Certified (graph core2466) (root 10) 4 0 :=
  of_native_maps core2466 DegreeTwoThreeSpectrum5393.graph DegreeTwoThreeSpectrum4992.graph
    sourceMap2466swap fusedMap2466swap sourceMap2466swap_checked fusedMap2466swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2466
#print axioms sourceMap2466swap_checked
#print axioms fusedMap2466swap_checked
#print axioms certified2466swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
