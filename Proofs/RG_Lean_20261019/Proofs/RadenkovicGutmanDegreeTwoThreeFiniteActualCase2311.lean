/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2311 : Family 9 := level9.get ⟨324,by decide⟩
def sourceMap2311 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2311 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2311_checked : acceptsGraphIso
    (source (graph core2311) (root 9) 0 4) DegreeTwoThreeSpectrum4191.graph sourceMap2311=true := by decide +kernel
theorem fusedMap2311_checked : acceptsGraphIso
    (fused (graph core2311) (root 9) 0 4) DegreeTwoThreeSpectrum4192.graph fusedMap2311=true := by decide +kernel
theorem certified2311 : Certified (graph core2311) (root 9) 0 4 :=
  of_native_maps core2311 DegreeTwoThreeSpectrum4191.graph DegreeTwoThreeSpectrum4192.graph
    sourceMap2311 fusedMap2311 sourceMap2311_checked fusedMap2311_checked
    DegreeTwoThreeFiniteComparisons.comparison2311
#print axioms sourceMap2311_checked
#print axioms fusedMap2311_checked
#print axioms certified2311
def sourceMap2311swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2311swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2311swap_checked : acceptsGraphIso
    (source (graph core2311) (root 9) 4 0) DegreeTwoThreeSpectrum4191.graph sourceMap2311swap=true := by decide +kernel
theorem fusedMap2311swap_checked : acceptsGraphIso
    (fused (graph core2311) (root 9) 4 0) DegreeTwoThreeSpectrum4192.graph fusedMap2311swap=true := by decide +kernel
theorem certified2311swap : Certified (graph core2311) (root 9) 4 0 :=
  of_native_maps core2311 DegreeTwoThreeSpectrum4191.graph DegreeTwoThreeSpectrum4192.graph
    sourceMap2311swap fusedMap2311swap sourceMap2311swap_checked fusedMap2311swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2311
#print axioms sourceMap2311swap_checked
#print axioms fusedMap2311swap_checked
#print axioms certified2311swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
