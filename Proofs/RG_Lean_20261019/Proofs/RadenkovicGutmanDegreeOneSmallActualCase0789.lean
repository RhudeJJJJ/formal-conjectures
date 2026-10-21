/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0789 : Family 8 := level8.get ⟨15,by decide⟩
def sourceMap0789 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0789 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0789_checked : acceptsGraphIso
    (source (graph core0789) (root 8) 0 2) DegreeOneSmallSpectrum920.graph sourceMap0789=true := by decide +kernel
theorem fusedMap0789_checked : acceptsGraphIso
    (fused (graph core0789) (root 8) 0 2) DegreeOneSmallSpectrum922.graph fusedMap0789=true := by decide +kernel
theorem certified0789 : Certified (graph core0789) (root 8) 0 2 :=
  of_native_maps core0789 DegreeOneSmallSpectrum920.graph DegreeOneSmallSpectrum922.graph
    sourceMap0789 fusedMap0789 sourceMap0789_checked fusedMap0789_checked
    DegreeOneSmallComparisons.comparison0789
#print axioms sourceMap0789_checked
#print axioms fusedMap0789_checked
#print axioms certified0789
def sourceMap0789swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0789swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0789swap_checked : acceptsGraphIso
    (source (graph core0789) (root 8) 2 0) DegreeOneSmallSpectrum920.graph sourceMap0789swap=true := by decide +kernel
theorem fusedMap0789swap_checked : acceptsGraphIso
    (fused (graph core0789) (root 8) 2 0) DegreeOneSmallSpectrum922.graph fusedMap0789swap=true := by decide +kernel
theorem certified0789swap : Certified (graph core0789) (root 8) 2 0 :=
  of_native_maps core0789 DegreeOneSmallSpectrum920.graph DegreeOneSmallSpectrum922.graph
    sourceMap0789swap fusedMap0789swap sourceMap0789swap_checked fusedMap0789swap_checked
    DegreeOneSmallComparisons.comparison0789
#print axioms sourceMap0789swap_checked
#print axioms fusedMap0789swap_checked
#print axioms certified0789swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
