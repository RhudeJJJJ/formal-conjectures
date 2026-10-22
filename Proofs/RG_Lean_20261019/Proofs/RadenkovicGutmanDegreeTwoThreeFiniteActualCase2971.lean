/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2971 : Family 10 := level10.get ⟨1480,by decide⟩
def sourceMap2971 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2971 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2971_checked : acceptsGraphIso
    (source (graph core2971) (root 10) 0 4) DegreeTwoThreeSpectrum6968.graph sourceMap2971=true := by decide +kernel
theorem fusedMap2971_checked : acceptsGraphIso
    (fused (graph core2971) (root 10) 0 4) DegreeTwoThreeSpectrum6969.graph fusedMap2971=true := by decide +kernel
theorem certified2971 : Certified (graph core2971) (root 10) 0 4 :=
  of_native_maps core2971 DegreeTwoThreeSpectrum6968.graph DegreeTwoThreeSpectrum6969.graph
    sourceMap2971 fusedMap2971 sourceMap2971_checked fusedMap2971_checked
    DegreeTwoThreeFiniteComparisons.comparison2971
#print axioms sourceMap2971_checked
#print axioms fusedMap2971_checked
#print axioms certified2971
def sourceMap2971swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2971swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2971swap_checked : acceptsGraphIso
    (source (graph core2971) (root 10) 4 0) DegreeTwoThreeSpectrum6968.graph sourceMap2971swap=true := by decide +kernel
theorem fusedMap2971swap_checked : acceptsGraphIso
    (fused (graph core2971) (root 10) 4 0) DegreeTwoThreeSpectrum6969.graph fusedMap2971swap=true := by decide +kernel
theorem certified2971swap : Certified (graph core2971) (root 10) 4 0 :=
  of_native_maps core2971 DegreeTwoThreeSpectrum6968.graph DegreeTwoThreeSpectrum6969.graph
    sourceMap2971swap fusedMap2971swap sourceMap2971swap_checked fusedMap2971swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2971
#print axioms sourceMap2971swap_checked
#print axioms fusedMap2971swap_checked
#print axioms certified2971swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
