/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0740 : Family 8 := level8.get ⟨1,by decide⟩
def sourceMap0740 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0740 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0740_checked : acceptsGraphIso
    (source (graph core0740) (root 8) 0 1) DegreeOneSmallSpectrum375.graph sourceMap0740=true := by decide +kernel
theorem fusedMap0740_checked : acceptsGraphIso
    (fused (graph core0740) (root 8) 0 1) DegreeOneSmallSpectrum378.graph fusedMap0740=true := by decide +kernel
theorem certified0740 : Certified (graph core0740) (root 8) 0 1 :=
  of_native_maps core0740 DegreeOneSmallSpectrum375.graph DegreeOneSmallSpectrum378.graph
    sourceMap0740 fusedMap0740 sourceMap0740_checked fusedMap0740_checked
    DegreeOneSmallComparisons.comparison0740
#print axioms sourceMap0740_checked
#print axioms fusedMap0740_checked
#print axioms certified0740
def sourceMap0740swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0740swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0740swap_checked : acceptsGraphIso
    (source (graph core0740) (root 8) 1 0) DegreeOneSmallSpectrum375.graph sourceMap0740swap=true := by decide +kernel
theorem fusedMap0740swap_checked : acceptsGraphIso
    (fused (graph core0740) (root 8) 1 0) DegreeOneSmallSpectrum378.graph fusedMap0740swap=true := by decide +kernel
theorem certified0740swap : Certified (graph core0740) (root 8) 1 0 :=
  of_native_maps core0740 DegreeOneSmallSpectrum375.graph DegreeOneSmallSpectrum378.graph
    sourceMap0740swap fusedMap0740swap sourceMap0740swap_checked fusedMap0740swap_checked
    DegreeOneSmallComparisons.comparison0740
#print axioms sourceMap0740swap_checked
#print axioms fusedMap0740swap_checked
#print axioms certified0740swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
