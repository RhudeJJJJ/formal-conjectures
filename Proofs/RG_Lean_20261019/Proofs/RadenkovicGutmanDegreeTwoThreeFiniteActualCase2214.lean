/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2214 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap2214 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2214 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2214_checked : acceptsGraphIso
    (source (graph core2214) (root 8) 0 4) DegreeTwoThreeSpectrum3059.graph sourceMap2214=true := by decide +kernel
theorem fusedMap2214_checked : acceptsGraphIso
    (fused (graph core2214) (root 8) 0 4) DegreeTwoThreeSpectrum3061.graph fusedMap2214=true := by decide +kernel
theorem certified2214 : Certified (graph core2214) (root 8) 0 4 :=
  of_native_maps core2214 DegreeTwoThreeSpectrum3059.graph DegreeTwoThreeSpectrum3061.graph
    sourceMap2214 fusedMap2214 sourceMap2214_checked fusedMap2214_checked
    DegreeTwoThreeFiniteComparisons.comparison2214
#print axioms sourceMap2214_checked
#print axioms fusedMap2214_checked
#print axioms certified2214
def sourceMap2214swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2214swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2214swap_checked : acceptsGraphIso
    (source (graph core2214) (root 8) 4 0) DegreeTwoThreeSpectrum3059.graph sourceMap2214swap=true := by decide +kernel
theorem fusedMap2214swap_checked : acceptsGraphIso
    (fused (graph core2214) (root 8) 4 0) DegreeTwoThreeSpectrum3061.graph fusedMap2214swap=true := by decide +kernel
theorem certified2214swap : Certified (graph core2214) (root 8) 4 0 :=
  of_native_maps core2214 DegreeTwoThreeSpectrum3059.graph DegreeTwoThreeSpectrum3061.graph
    sourceMap2214swap fusedMap2214swap sourceMap2214swap_checked fusedMap2214swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2214
#print axioms sourceMap2214swap_checked
#print axioms fusedMap2214swap_checked
#print axioms certified2214swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
