/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1917 : Family 10 := level10.get ⟨204,by decide⟩
def sourceMap1917 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1917 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1917_checked : acceptsGraphIso
    (source (graph core1917) (root 10) 0 0) DegreeOneSmallSpectrum1050.graph sourceMap1917=true := by decide +kernel
theorem fusedMap1917_checked : acceptsGraphIso
    (fused (graph core1917) (root 10) 0 0) DegreeOneSmallSpectrum1058.graph fusedMap1917=true := by decide +kernel
theorem certified1917 : Certified (graph core1917) (root 10) 0 0 :=
  of_native_maps core1917 DegreeOneSmallSpectrum1050.graph DegreeOneSmallSpectrum1058.graph
    sourceMap1917 fusedMap1917 sourceMap1917_checked fusedMap1917_checked
    DegreeOneSmallComparisons.comparison1917
#print axioms sourceMap1917_checked
#print axioms fusedMap1917_checked
#print axioms certified1917
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
