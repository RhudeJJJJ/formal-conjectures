/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2472 : Family 10 := level10.get ⟨104,by decide⟩
def sourceMap2472 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2472 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2472_checked : acceptsGraphIso
    (source (graph core2472) (root 10) 0 4) DegreeTwoThreeSpectrum5593.graph sourceMap2472=true := by decide +kernel
theorem fusedMap2472_checked : acceptsGraphIso
    (fused (graph core2472) (root 10) 0 4) DegreeTwoThreeSpectrum5026.graph fusedMap2472=true := by decide +kernel
theorem certified2472 : Certified (graph core2472) (root 10) 0 4 :=
  of_native_maps core2472 DegreeTwoThreeSpectrum5593.graph DegreeTwoThreeSpectrum5026.graph
    sourceMap2472 fusedMap2472 sourceMap2472_checked fusedMap2472_checked
    DegreeTwoThreeFiniteComparisons.comparison2472
#print axioms sourceMap2472_checked
#print axioms fusedMap2472_checked
#print axioms certified2472
def sourceMap2472swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2472swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2472swap_checked : acceptsGraphIso
    (source (graph core2472) (root 10) 4 0) DegreeTwoThreeSpectrum5593.graph sourceMap2472swap=true := by decide +kernel
theorem fusedMap2472swap_checked : acceptsGraphIso
    (fused (graph core2472) (root 10) 4 0) DegreeTwoThreeSpectrum5026.graph fusedMap2472swap=true := by decide +kernel
theorem certified2472swap : Certified (graph core2472) (root 10) 4 0 :=
  of_native_maps core2472 DegreeTwoThreeSpectrum5593.graph DegreeTwoThreeSpectrum5026.graph
    sourceMap2472swap fusedMap2472swap sourceMap2472swap_checked fusedMap2472swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2472
#print axioms sourceMap2472swap_checked
#print axioms fusedMap2472swap_checked
#print axioms certified2472swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
