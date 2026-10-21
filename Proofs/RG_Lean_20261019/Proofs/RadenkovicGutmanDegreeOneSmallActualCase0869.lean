/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0869 : Family 8 := level8.get ⟨42,by decide⟩
def sourceMap0869 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0869 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0869_checked : acceptsGraphIso
    (source (graph core0869) (root 8) 0 2) DegreeOneSmallSpectrum1180.graph sourceMap0869=true := by decide +kernel
theorem fusedMap0869_checked : acceptsGraphIso
    (fused (graph core0869) (root 8) 0 2) DegreeOneSmallSpectrum874.graph fusedMap0869=true := by decide +kernel
theorem certified0869 : Certified (graph core0869) (root 8) 0 2 :=
  of_native_maps core0869 DegreeOneSmallSpectrum1180.graph DegreeOneSmallSpectrum874.graph
    sourceMap0869 fusedMap0869 sourceMap0869_checked fusedMap0869_checked
    DegreeOneSmallComparisons.comparison0869
#print axioms sourceMap0869_checked
#print axioms fusedMap0869_checked
#print axioms certified0869
def sourceMap0869swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0869swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0869swap_checked : acceptsGraphIso
    (source (graph core0869) (root 8) 2 0) DegreeOneSmallSpectrum1180.graph sourceMap0869swap=true := by decide +kernel
theorem fusedMap0869swap_checked : acceptsGraphIso
    (fused (graph core0869) (root 8) 2 0) DegreeOneSmallSpectrum874.graph fusedMap0869swap=true := by decide +kernel
theorem certified0869swap : Certified (graph core0869) (root 8) 2 0 :=
  of_native_maps core0869 DegreeOneSmallSpectrum1180.graph DegreeOneSmallSpectrum874.graph
    sourceMap0869swap fusedMap0869swap sourceMap0869swap_checked fusedMap0869swap_checked
    DegreeOneSmallComparisons.comparison0869
#print axioms sourceMap0869swap_checked
#print axioms fusedMap0869swap_checked
#print axioms certified0869swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
