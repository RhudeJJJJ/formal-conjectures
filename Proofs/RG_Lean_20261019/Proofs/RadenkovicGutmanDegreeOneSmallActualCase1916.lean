/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1916 : Family 10 := level10.get ⟨203,by decide⟩
def sourceMap1916 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1916 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1916_checked : acceptsGraphIso
    (source (graph core1916) (root 10) 0 0) DegreeOneSmallSpectrum1051.graph sourceMap1916=true := by decide +kernel
theorem fusedMap1916_checked : acceptsGraphIso
    (fused (graph core1916) (root 10) 0 0) DegreeOneSmallSpectrum1059.graph fusedMap1916=true := by decide +kernel
theorem certified1916 : Certified (graph core1916) (root 10) 0 0 :=
  of_native_maps core1916 DegreeOneSmallSpectrum1051.graph DegreeOneSmallSpectrum1059.graph
    sourceMap1916 fusedMap1916 sourceMap1916_checked fusedMap1916_checked
    DegreeOneSmallComparisons.comparison1916
#print axioms sourceMap1916_checked
#print axioms fusedMap1916_checked
#print axioms certified1916
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
