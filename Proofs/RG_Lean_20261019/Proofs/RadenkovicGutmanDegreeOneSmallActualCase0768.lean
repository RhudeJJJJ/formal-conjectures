/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0768 : Family 8 := level8.get ⟨9,by decide⟩
def sourceMap0768 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0768 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0768_checked : acceptsGraphIso
    (source (graph core0768) (root 8) 0 1) DegreeOneSmallSpectrum453.graph sourceMap0768=true := by decide +kernel
theorem fusedMap0768_checked : acceptsGraphIso
    (fused (graph core0768) (root 8) 0 1) DegreeOneSmallSpectrum371.graph fusedMap0768=true := by decide +kernel
theorem certified0768 : Certified (graph core0768) (root 8) 0 1 :=
  of_native_maps core0768 DegreeOneSmallSpectrum453.graph DegreeOneSmallSpectrum371.graph
    sourceMap0768 fusedMap0768 sourceMap0768_checked fusedMap0768_checked
    DegreeOneSmallComparisons.comparison0768
#print axioms sourceMap0768_checked
#print axioms fusedMap0768_checked
#print axioms certified0768
def sourceMap0768swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0768swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0768swap_checked : acceptsGraphIso
    (source (graph core0768) (root 8) 1 0) DegreeOneSmallSpectrum453.graph sourceMap0768swap=true := by decide +kernel
theorem fusedMap0768swap_checked : acceptsGraphIso
    (fused (graph core0768) (root 8) 1 0) DegreeOneSmallSpectrum371.graph fusedMap0768swap=true := by decide +kernel
theorem certified0768swap : Certified (graph core0768) (root 8) 1 0 :=
  of_native_maps core0768 DegreeOneSmallSpectrum453.graph DegreeOneSmallSpectrum371.graph
    sourceMap0768swap fusedMap0768swap sourceMap0768swap_checked fusedMap0768swap_checked
    DegreeOneSmallComparisons.comparison0768
#print axioms sourceMap0768swap_checked
#print axioms fusedMap0768swap_checked
#print axioms certified0768swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
