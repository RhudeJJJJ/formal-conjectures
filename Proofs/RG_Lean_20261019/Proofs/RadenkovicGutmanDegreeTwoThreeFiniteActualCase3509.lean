/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3509 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap3509 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3509 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3509_checked : acceptsGraphIso
    (source (graph core3509) (root 7) 0 6) DegreeTwoThreeSpectrum3933.graph sourceMap3509=true := by decide +kernel
theorem fusedMap3509_checked : acceptsGraphIso
    (fused (graph core3509) (root 7) 0 6) DegreeTwoThreeSpectrum3935.graph fusedMap3509=true := by decide +kernel
theorem certified3509 : Certified (graph core3509) (root 7) 0 6 :=
  of_native_maps core3509 DegreeTwoThreeSpectrum3933.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap3509 fusedMap3509 sourceMap3509_checked fusedMap3509_checked
    DegreeTwoThreeFiniteComparisons.comparison3509
#print axioms sourceMap3509_checked
#print axioms fusedMap3509_checked
#print axioms certified3509
def sourceMap3509swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3509swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3509swap_checked : acceptsGraphIso
    (source (graph core3509) (root 7) 6 0) DegreeTwoThreeSpectrum3933.graph sourceMap3509swap=true := by decide +kernel
theorem fusedMap3509swap_checked : acceptsGraphIso
    (fused (graph core3509) (root 7) 6 0) DegreeTwoThreeSpectrum3935.graph fusedMap3509swap=true := by decide +kernel
theorem certified3509swap : Certified (graph core3509) (root 7) 6 0 :=
  of_native_maps core3509 DegreeTwoThreeSpectrum3933.graph DegreeTwoThreeSpectrum3935.graph
    sourceMap3509swap fusedMap3509swap sourceMap3509swap_checked fusedMap3509swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3509
#print axioms sourceMap3509swap_checked
#print axioms fusedMap3509swap_checked
#print axioms certified3509swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
