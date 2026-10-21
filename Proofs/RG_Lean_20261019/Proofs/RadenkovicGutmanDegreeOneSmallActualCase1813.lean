/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1813 : Family 10 := level10.get ⟨56,by decide⟩
def sourceMap1813 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1813 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1813_checked : acceptsGraphIso
    (source (graph core1813) (root 10) 0 0) DegreeOneSmallSpectrum1067.graph sourceMap1813=true := by decide +kernel
theorem fusedMap1813_checked : acceptsGraphIso
    (fused (graph core1813) (root 10) 0 0) DegreeOneSmallSpectrum865.graph fusedMap1813=true := by decide +kernel
theorem certified1813 : Certified (graph core1813) (root 10) 0 0 :=
  of_native_maps core1813 DegreeOneSmallSpectrum1067.graph DegreeOneSmallSpectrum865.graph
    sourceMap1813 fusedMap1813 sourceMap1813_checked fusedMap1813_checked
    DegreeOneSmallComparisons.comparison1813
#print axioms sourceMap1813_checked
#print axioms fusedMap1813_checked
#print axioms certified1813
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
