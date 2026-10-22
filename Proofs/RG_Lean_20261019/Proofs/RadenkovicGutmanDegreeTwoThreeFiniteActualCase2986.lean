/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2986 : Family 10 := level10.get ⟨1536,by decide⟩
def sourceMap2986 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2986 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2986_checked : acceptsGraphIso
    (source (graph core2986) (root 10) 0 4) DegreeTwoThreeSpectrum7074.graph sourceMap2986=true := by decide +kernel
theorem fusedMap2986_checked : acceptsGraphIso
    (fused (graph core2986) (root 10) 0 4) DegreeTwoThreeSpectrum5977.graph fusedMap2986=true := by decide +kernel
theorem certified2986 : Certified (graph core2986) (root 10) 0 4 :=
  of_native_maps core2986 DegreeTwoThreeSpectrum7074.graph DegreeTwoThreeSpectrum5977.graph
    sourceMap2986 fusedMap2986 sourceMap2986_checked fusedMap2986_checked
    DegreeTwoThreeFiniteComparisons.comparison2986
#print axioms sourceMap2986_checked
#print axioms fusedMap2986_checked
#print axioms certified2986
def sourceMap2986swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap2986swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2986swap_checked : acceptsGraphIso
    (source (graph core2986) (root 10) 4 0) DegreeTwoThreeSpectrum7074.graph sourceMap2986swap=true := by decide +kernel
theorem fusedMap2986swap_checked : acceptsGraphIso
    (fused (graph core2986) (root 10) 4 0) DegreeTwoThreeSpectrum5977.graph fusedMap2986swap=true := by decide +kernel
theorem certified2986swap : Certified (graph core2986) (root 10) 4 0 :=
  of_native_maps core2986 DegreeTwoThreeSpectrum7074.graph DegreeTwoThreeSpectrum5977.graph
    sourceMap2986swap fusedMap2986swap sourceMap2986swap_checked fusedMap2986swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2986
#print axioms sourceMap2986swap_checked
#print axioms fusedMap2986swap_checked
#print axioms certified2986swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
