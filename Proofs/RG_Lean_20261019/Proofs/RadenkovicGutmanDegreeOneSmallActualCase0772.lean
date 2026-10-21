/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0772 : Family 8 := level8.get ⟨10,by decide⟩
def sourceMap0772 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0772 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0772_checked : acceptsGraphIso
    (source (graph core0772) (root 8) 0 1) DegreeOneSmallSpectrum475.graph sourceMap0772=true := by decide +kernel
theorem fusedMap0772_checked : acceptsGraphIso
    (fused (graph core0772) (root 8) 0 1) DegreeOneSmallSpectrum372.graph fusedMap0772=true := by decide +kernel
theorem certified0772 : Certified (graph core0772) (root 8) 0 1 :=
  of_native_maps core0772 DegreeOneSmallSpectrum475.graph DegreeOneSmallSpectrum372.graph
    sourceMap0772 fusedMap0772 sourceMap0772_checked fusedMap0772_checked
    DegreeOneSmallComparisons.comparison0772
#print axioms sourceMap0772_checked
#print axioms fusedMap0772_checked
#print axioms certified0772
def sourceMap0772swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0772swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0772swap_checked : acceptsGraphIso
    (source (graph core0772) (root 8) 1 0) DegreeOneSmallSpectrum475.graph sourceMap0772swap=true := by decide +kernel
theorem fusedMap0772swap_checked : acceptsGraphIso
    (fused (graph core0772) (root 8) 1 0) DegreeOneSmallSpectrum372.graph fusedMap0772swap=true := by decide +kernel
theorem certified0772swap : Certified (graph core0772) (root 8) 1 0 :=
  of_native_maps core0772 DegreeOneSmallSpectrum475.graph DegreeOneSmallSpectrum372.graph
    sourceMap0772swap fusedMap0772swap sourceMap0772swap_checked fusedMap0772swap_checked
    DegreeOneSmallComparisons.comparison0772
#print axioms sourceMap0772swap_checked
#print axioms fusedMap0772swap_checked
#print axioms certified0772swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
