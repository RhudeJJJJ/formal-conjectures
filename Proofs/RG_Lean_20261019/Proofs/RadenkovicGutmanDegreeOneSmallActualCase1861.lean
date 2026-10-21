/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1861 : Family 10 := level10.get ⟨120,by decide⟩
def sourceMap1861 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1861 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1861_checked : acceptsGraphIso
    (source (graph core1861) (root 10) 0 0) DegreeOneSmallSpectrum1278.graph sourceMap1861=true := by decide +kernel
theorem fusedMap1861_checked : acceptsGraphIso
    (fused (graph core1861) (root 10) 0 0) DegreeOneSmallSpectrum946.graph fusedMap1861=true := by decide +kernel
theorem certified1861 : Certified (graph core1861) (root 10) 0 0 :=
  of_native_maps core1861 DegreeOneSmallSpectrum1278.graph DegreeOneSmallSpectrum946.graph
    sourceMap1861 fusedMap1861 sourceMap1861_checked fusedMap1861_checked
    DegreeOneSmallComparisons.comparison1861
#print axioms sourceMap1861_checked
#print axioms fusedMap1861_checked
#print axioms certified1861
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
