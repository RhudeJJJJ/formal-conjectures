/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0889 : Family 8 := level8.get ⟨49,by decide⟩
def sourceMap0889 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,10,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap0889 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0889_checked : acceptsGraphIso
    (source (graph core0889) (root 8) 0 2) DegreeOneSmallSpectrum1287.graph sourceMap0889=true := by decide +kernel
theorem fusedMap0889_checked : acceptsGraphIso
    (fused (graph core0889) (root 8) 0 2) DegreeOneSmallSpectrum889.graph fusedMap0889=true := by decide +kernel
theorem certified0889 : Certified (graph core0889) (root 8) 0 2 :=
  of_native_maps core0889 DegreeOneSmallSpectrum1287.graph DegreeOneSmallSpectrum889.graph
    sourceMap0889 fusedMap0889 sourceMap0889_checked fusedMap0889_checked
    DegreeOneSmallComparisons.comparison0889
#print axioms sourceMap0889_checked
#print axioms fusedMap0889_checked
#print axioms certified0889
def sourceMap0889swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 2 0 v)
def fusedMap0889swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0889swap_checked : acceptsGraphIso
    (source (graph core0889) (root 8) 2 0) DegreeOneSmallSpectrum1287.graph sourceMap0889swap=true := by decide +kernel
theorem fusedMap0889swap_checked : acceptsGraphIso
    (fused (graph core0889) (root 8) 2 0) DegreeOneSmallSpectrum889.graph fusedMap0889swap=true := by decide +kernel
theorem certified0889swap : Certified (graph core0889) (root 8) 2 0 :=
  of_native_maps core0889 DegreeOneSmallSpectrum1287.graph DegreeOneSmallSpectrum889.graph
    sourceMap0889swap fusedMap0889swap sourceMap0889swap_checked fusedMap0889swap_checked
    DegreeOneSmallComparisons.comparison0889
#print axioms sourceMap0889swap_checked
#print axioms fusedMap0889swap_checked
#print axioms certified0889swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
