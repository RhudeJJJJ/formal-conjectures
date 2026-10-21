/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0905 : Family 8 := level8.get ⟨57,by decide⟩
def sourceMap0905 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0905 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0905_checked : acceptsGraphIso
    (source (graph core0905) (root 8) 0 2) DegreeOneSmallSpectrum1363.graph sourceMap0905=true := by decide +kernel
theorem fusedMap0905_checked : acceptsGraphIso
    (fused (graph core0905) (root 8) 0 2) DegreeOneSmallSpectrum916.graph fusedMap0905=true := by decide +kernel
theorem certified0905 : Certified (graph core0905) (root 8) 0 2 :=
  of_native_maps core0905 DegreeOneSmallSpectrum1363.graph DegreeOneSmallSpectrum916.graph
    sourceMap0905 fusedMap0905 sourceMap0905_checked fusedMap0905_checked
    DegreeOneSmallComparisons.comparison0905
#print axioms sourceMap0905_checked
#print axioms fusedMap0905_checked
#print axioms certified0905
def sourceMap0905swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0905swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0905swap_checked : acceptsGraphIso
    (source (graph core0905) (root 8) 2 0) DegreeOneSmallSpectrum1363.graph sourceMap0905swap=true := by decide +kernel
theorem fusedMap0905swap_checked : acceptsGraphIso
    (fused (graph core0905) (root 8) 2 0) DegreeOneSmallSpectrum916.graph fusedMap0905swap=true := by decide +kernel
theorem certified0905swap : Certified (graph core0905) (root 8) 2 0 :=
  of_native_maps core0905 DegreeOneSmallSpectrum1363.graph DegreeOneSmallSpectrum916.graph
    sourceMap0905swap fusedMap0905swap sourceMap0905swap_checked fusedMap0905swap_checked
    DegreeOneSmallComparisons.comparison0905
#print axioms sourceMap0905swap_checked
#print axioms fusedMap0905swap_checked
#print axioms certified0905swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
