/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0666 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0666 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0666 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0666_checked : acceptsGraphIso
    (source (graph core0666) (root 7) 0 3) DegreeOneSmallSpectrum1497.graph sourceMap0666=true := by decide +kernel
theorem fusedMap0666_checked : acceptsGraphIso
    (fused (graph core0666) (root 7) 0 3) DegreeOneSmallSpectrum952.graph fusedMap0666=true := by decide +kernel
theorem certified0666 : Certified (graph core0666) (root 7) 0 3 :=
  of_native_maps core0666 DegreeOneSmallSpectrum1497.graph DegreeOneSmallSpectrum952.graph
    sourceMap0666 fusedMap0666 sourceMap0666_checked fusedMap0666_checked
    DegreeOneSmallComparisons.comparison0666
#print axioms sourceMap0666_checked
#print axioms fusedMap0666_checked
#print axioms certified0666
def sourceMap0666swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0666swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0666swap_checked : acceptsGraphIso
    (source (graph core0666) (root 7) 3 0) DegreeOneSmallSpectrum1497.graph sourceMap0666swap=true := by decide +kernel
theorem fusedMap0666swap_checked : acceptsGraphIso
    (fused (graph core0666) (root 7) 3 0) DegreeOneSmallSpectrum952.graph fusedMap0666swap=true := by decide +kernel
theorem certified0666swap : Certified (graph core0666) (root 7) 3 0 :=
  of_native_maps core0666 DegreeOneSmallSpectrum1497.graph DegreeOneSmallSpectrum952.graph
    sourceMap0666swap fusedMap0666swap sourceMap0666swap_checked fusedMap0666swap_checked
    DegreeOneSmallComparisons.comparison0666
#print axioms sourceMap0666swap_checked
#print axioms fusedMap0666swap_checked
#print axioms certified0666swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
