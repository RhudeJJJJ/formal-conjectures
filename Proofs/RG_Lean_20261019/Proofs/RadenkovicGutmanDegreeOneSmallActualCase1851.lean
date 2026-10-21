/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1851 : Family 10 := level10.get ⟨105,by decide⟩
def sourceMap1851 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1851 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1851_checked : acceptsGraphIso
    (source (graph core1851) (root 10) 0 0) DegreeOneSmallSpectrum1272.graph sourceMap1851=true := by decide +kernel
theorem fusedMap1851_checked : acceptsGraphIso
    (fused (graph core1851) (root 10) 0 0) DegreeOneSmallSpectrum930.graph fusedMap1851=true := by decide +kernel
theorem certified1851 : Certified (graph core1851) (root 10) 0 0 :=
  of_native_maps core1851 DegreeOneSmallSpectrum1272.graph DegreeOneSmallSpectrum930.graph
    sourceMap1851 fusedMap1851 sourceMap1851_checked fusedMap1851_checked
    DegreeOneSmallComparisons.comparison1851
#print axioms sourceMap1851_checked
#print axioms fusedMap1851_checked
#print axioms certified1851
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
