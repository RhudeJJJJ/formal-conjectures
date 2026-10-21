/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0904 : Family 8 := level8.get ⟨57,by decide⟩
def sourceMap0904 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0904 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0904_checked : acceptsGraphIso
    (source (graph core0904) (root 8) 0 1) SmallGeFourSpectrum102.graph sourceMap0904=true := by decide +kernel
theorem fusedMap0904_checked : acceptsGraphIso
    (fused (graph core0904) (root 8) 0 1) SmallGeFourSpectrum104.graph fusedMap0904=true := by decide +kernel
theorem certified0904 : Certified (graph core0904) (root 8) 0 1 :=
  of_native_maps core0904 SmallGeFourSpectrum102.graph SmallGeFourSpectrum104.graph
    sourceMap0904 fusedMap0904 sourceMap0904_checked fusedMap0904_checked
    DegreeOneSmallComparisons.comparison0904
#print axioms sourceMap0904_checked
#print axioms fusedMap0904_checked
#print axioms certified0904
def sourceMap0904swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0904swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0904swap_checked : acceptsGraphIso
    (source (graph core0904) (root 8) 1 0) SmallGeFourSpectrum102.graph sourceMap0904swap=true := by decide +kernel
theorem fusedMap0904swap_checked : acceptsGraphIso
    (fused (graph core0904) (root 8) 1 0) SmallGeFourSpectrum104.graph fusedMap0904swap=true := by decide +kernel
theorem certified0904swap : Certified (graph core0904) (root 8) 1 0 :=
  of_native_maps core0904 SmallGeFourSpectrum102.graph SmallGeFourSpectrum104.graph
    sourceMap0904swap fusedMap0904swap sourceMap0904swap_checked fusedMap0904swap_checked
    DegreeOneSmallComparisons.comparison0904
#print axioms sourceMap0904swap_checked
#print axioms fusedMap0904swap_checked
#print axioms certified0904swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
