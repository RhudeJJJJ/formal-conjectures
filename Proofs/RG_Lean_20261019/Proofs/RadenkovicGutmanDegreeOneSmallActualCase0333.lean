/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0333 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0333 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0333 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0333_checked : acceptsGraphIso
    (source (graph core0333) (root 6) 0 3) DegreeOneSmallSpectrum479.graph sourceMap0333=true := by decide +kernel
theorem fusedMap0333_checked : acceptsGraphIso
    (fused (graph core0333) (root 6) 0 3) DegreeOneSmallSpectrum372.graph fusedMap0333=true := by decide +kernel
theorem certified0333 : Certified (graph core0333) (root 6) 0 3 :=
  of_native_maps core0333 DegreeOneSmallSpectrum479.graph DegreeOneSmallSpectrum372.graph
    sourceMap0333 fusedMap0333 sourceMap0333_checked fusedMap0333_checked
    DegreeOneSmallComparisons.comparison0333
#print axioms sourceMap0333_checked
#print axioms fusedMap0333_checked
#print axioms certified0333
def sourceMap0333swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0333swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0333swap_checked : acceptsGraphIso
    (source (graph core0333) (root 6) 3 0) DegreeOneSmallSpectrum479.graph sourceMap0333swap=true := by decide +kernel
theorem fusedMap0333swap_checked : acceptsGraphIso
    (fused (graph core0333) (root 6) 3 0) DegreeOneSmallSpectrum372.graph fusedMap0333swap=true := by decide +kernel
theorem certified0333swap : Certified (graph core0333) (root 6) 3 0 :=
  of_native_maps core0333 DegreeOneSmallSpectrum479.graph DegreeOneSmallSpectrum372.graph
    sourceMap0333swap fusedMap0333swap sourceMap0333swap_checked fusedMap0333swap_checked
    DegreeOneSmallComparisons.comparison0333
#print axioms sourceMap0333swap_checked
#print axioms fusedMap0333swap_checked
#print axioms certified0333swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
