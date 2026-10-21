/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1014 : Family 8 := level8.get ⟨104,by decide⟩
def sourceMap1014 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 8 1 1 v)
def fusedMap1014 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1014_checked : acceptsGraphIso
    (source (graph core1014) (root 8) 1 1) DegreeOneSmallSpectrum1686.graph sourceMap1014=true := by decide +kernel
theorem fusedMap1014_checked : acceptsGraphIso
    (fused (graph core1014) (root 8) 1 1) DegreeOneSmallSpectrum1049.graph fusedMap1014=true := by decide +kernel
theorem certified1014 : Certified (graph core1014) (root 8) 1 1 :=
  of_native_maps core1014 DegreeOneSmallSpectrum1686.graph DegreeOneSmallSpectrum1049.graph
    sourceMap1014 fusedMap1014 sourceMap1014_checked fusedMap1014_checked
    DegreeOneSmallComparisons.comparison1014
#print axioms sourceMap1014_checked
#print axioms fusedMap1014_checked
#print axioms certified1014
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
