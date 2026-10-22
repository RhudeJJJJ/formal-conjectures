/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2547 : Family 10 := level10.get ⟨370,by decide⟩
def sourceMap2547 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2547 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2547_checked : acceptsGraphIso
    (source (graph core2547) (root 10) 0 4) DegreeTwoThreeSpectrum5669.graph sourceMap2547=true := by decide +kernel
theorem fusedMap2547_checked : acceptsGraphIso
    (fused (graph core2547) (root 10) 0 4) DegreeTwoThreeSpectrum5670.graph fusedMap2547=true := by decide +kernel
theorem certified2547 : Certified (graph core2547) (root 10) 0 4 :=
  of_native_maps core2547 DegreeTwoThreeSpectrum5669.graph DegreeTwoThreeSpectrum5670.graph
    sourceMap2547 fusedMap2547 sourceMap2547_checked fusedMap2547_checked
    DegreeTwoThreeFiniteComparisons.comparison2547
#print axioms sourceMap2547_checked
#print axioms fusedMap2547_checked
#print axioms certified2547
def sourceMap2547swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2547swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2547swap_checked : acceptsGraphIso
    (source (graph core2547) (root 10) 4 0) DegreeTwoThreeSpectrum5669.graph sourceMap2547swap=true := by decide +kernel
theorem fusedMap2547swap_checked : acceptsGraphIso
    (fused (graph core2547) (root 10) 4 0) DegreeTwoThreeSpectrum5670.graph fusedMap2547swap=true := by decide +kernel
theorem certified2547swap : Certified (graph core2547) (root 10) 4 0 :=
  of_native_maps core2547 DegreeTwoThreeSpectrum5669.graph DegreeTwoThreeSpectrum5670.graph
    sourceMap2547swap fusedMap2547swap sourceMap2547swap_checked fusedMap2547swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2547
#print axioms sourceMap2547swap_checked
#print axioms fusedMap2547swap_checked
#print axioms certified2547swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
