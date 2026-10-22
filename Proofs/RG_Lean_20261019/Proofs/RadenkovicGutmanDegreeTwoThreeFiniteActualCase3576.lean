/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3576 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap3576 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3576 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3576_checked : acceptsGraphIso
    (source (graph core3576) (root 8) 0 6) DegreeTwoThreeSpectrum5365.graph sourceMap3576=true := by decide +kernel
theorem fusedMap3576_checked : acceptsGraphIso
    (fused (graph core3576) (root 8) 0 6) DegreeTwoThreeSpectrum5367.graph fusedMap3576=true := by decide +kernel
theorem certified3576 : Certified (graph core3576) (root 8) 0 6 :=
  of_native_maps core3576 DegreeTwoThreeSpectrum5365.graph DegreeTwoThreeSpectrum5367.graph
    sourceMap3576 fusedMap3576 sourceMap3576_checked fusedMap3576_checked
    DegreeTwoThreeFiniteComparisons.comparison3576
#print axioms sourceMap3576_checked
#print axioms fusedMap3576_checked
#print axioms certified3576
def sourceMap3576swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3576swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3576swap_checked : acceptsGraphIso
    (source (graph core3576) (root 8) 6 0) DegreeTwoThreeSpectrum5365.graph sourceMap3576swap=true := by decide +kernel
theorem fusedMap3576swap_checked : acceptsGraphIso
    (fused (graph core3576) (root 8) 6 0) DegreeTwoThreeSpectrum5367.graph fusedMap3576swap=true := by decide +kernel
theorem certified3576swap : Certified (graph core3576) (root 8) 6 0 :=
  of_native_maps core3576 DegreeTwoThreeSpectrum5365.graph DegreeTwoThreeSpectrum5367.graph
    sourceMap3576swap fusedMap3576swap sourceMap3576swap_checked fusedMap3576swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3576
#print axioms sourceMap3576swap_checked
#print axioms fusedMap3576swap_checked
#print axioms certified3576swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
