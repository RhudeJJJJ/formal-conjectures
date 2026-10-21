/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0232 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0232 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0232 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0232_checked : acceptsGraphIso
    (source (graph core0232) (root 5) 0 1) DegreeOneSmallSpectrum054.graph sourceMap0232=true := by decide +kernel
theorem fusedMap0232_checked : acceptsGraphIso
    (fused (graph core0232) (root 5) 0 1) DegreeOneSmallSpectrum055.graph fusedMap0232=true := by decide +kernel
theorem certified0232 : Certified (graph core0232) (root 5) 0 1 :=
  of_native_maps core0232 DegreeOneSmallSpectrum054.graph DegreeOneSmallSpectrum055.graph
    sourceMap0232 fusedMap0232 sourceMap0232_checked fusedMap0232_checked
    DegreeOneSmallComparisons.comparison0232
#print axioms sourceMap0232_checked
#print axioms fusedMap0232_checked
#print axioms certified0232
def sourceMap0232swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0232swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0232swap_checked : acceptsGraphIso
    (source (graph core0232) (root 5) 1 0) DegreeOneSmallSpectrum054.graph sourceMap0232swap=true := by decide +kernel
theorem fusedMap0232swap_checked : acceptsGraphIso
    (fused (graph core0232) (root 5) 1 0) DegreeOneSmallSpectrum055.graph fusedMap0232swap=true := by decide +kernel
theorem certified0232swap : Certified (graph core0232) (root 5) 1 0 :=
  of_native_maps core0232 DegreeOneSmallSpectrum054.graph DegreeOneSmallSpectrum055.graph
    sourceMap0232swap fusedMap0232swap sourceMap0232swap_checked fusedMap0232swap_checked
    DegreeOneSmallComparisons.comparison0232
#print axioms sourceMap0232swap_checked
#print axioms fusedMap0232swap_checked
#print axioms certified0232swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
