/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0840 : Family 8 := level8.get ⟨34,by decide⟩
def sourceMap0840 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0840 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0840_checked : acceptsGraphIso
    (source (graph core0840) (root 8) 0 1) DegreeOneSmallSpectrum402.graph sourceMap0840=true := by decide +kernel
theorem fusedMap0840_checked : acceptsGraphIso
    (fused (graph core0840) (root 8) 0 1) SmallGeFourSpectrum094.graph fusedMap0840=true := by decide +kernel
theorem certified0840 : Certified (graph core0840) (root 8) 0 1 :=
  of_native_maps core0840 DegreeOneSmallSpectrum402.graph SmallGeFourSpectrum094.graph
    sourceMap0840 fusedMap0840 sourceMap0840_checked fusedMap0840_checked
    DegreeOneSmallComparisons.comparison0840
#print axioms sourceMap0840_checked
#print axioms fusedMap0840_checked
#print axioms certified0840
def sourceMap0840swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0840swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0840swap_checked : acceptsGraphIso
    (source (graph core0840) (root 8) 1 0) DegreeOneSmallSpectrum402.graph sourceMap0840swap=true := by decide +kernel
theorem fusedMap0840swap_checked : acceptsGraphIso
    (fused (graph core0840) (root 8) 1 0) SmallGeFourSpectrum094.graph fusedMap0840swap=true := by decide +kernel
theorem certified0840swap : Certified (graph core0840) (root 8) 1 0 :=
  of_native_maps core0840 DegreeOneSmallSpectrum402.graph SmallGeFourSpectrum094.graph
    sourceMap0840swap fusedMap0840swap sourceMap0840swap_checked fusedMap0840swap_checked
    DegreeOneSmallComparisons.comparison0840
#print axioms sourceMap0840swap_checked
#print axioms fusedMap0840swap_checked
#print axioms certified0840swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
