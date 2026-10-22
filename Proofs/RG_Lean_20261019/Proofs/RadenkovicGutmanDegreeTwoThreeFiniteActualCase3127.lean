/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3127 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap3127 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3127 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3127_checked : acceptsGraphIso
    (source (graph core3127) (root 7) 0 5) DegreeTwoThreeSpectrum2534.graph sourceMap3127=true := by decide +kernel
theorem fusedMap3127_checked : acceptsGraphIso
    (fused (graph core3127) (root 7) 0 5) DegreeTwoThreeSpectrum2536.graph fusedMap3127=true := by decide +kernel
theorem certified3127 : Certified (graph core3127) (root 7) 0 5 :=
  of_native_maps core3127 DegreeTwoThreeSpectrum2534.graph DegreeTwoThreeSpectrum2536.graph
    sourceMap3127 fusedMap3127 sourceMap3127_checked fusedMap3127_checked
    DegreeTwoThreeFiniteComparisons.comparison3127
#print axioms sourceMap3127_checked
#print axioms fusedMap3127_checked
#print axioms certified3127
def sourceMap3127swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3127swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3127swap_checked : acceptsGraphIso
    (source (graph core3127) (root 7) 5 0) DegreeTwoThreeSpectrum2534.graph sourceMap3127swap=true := by decide +kernel
theorem fusedMap3127swap_checked : acceptsGraphIso
    (fused (graph core3127) (root 7) 5 0) DegreeTwoThreeSpectrum2536.graph fusedMap3127swap=true := by decide +kernel
theorem certified3127swap : Certified (graph core3127) (root 7) 5 0 :=
  of_native_maps core3127 DegreeTwoThreeSpectrum2534.graph DegreeTwoThreeSpectrum2536.graph
    sourceMap3127swap fusedMap3127swap sourceMap3127swap_checked fusedMap3127swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3127
#print axioms sourceMap3127swap_checked
#print axioms fusedMap3127swap_checked
#print axioms certified3127swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
