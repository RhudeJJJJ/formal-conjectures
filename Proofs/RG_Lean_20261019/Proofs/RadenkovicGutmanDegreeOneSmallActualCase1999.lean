/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1999 : Family 10 := level10.get ⟨330,by decide⟩
def sourceMap1999 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1999 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1999_checked : acceptsGraphIso
    (source (graph core1999) (root 10) 0 0) DegreeOneSmallSpectrum1236.graph sourceMap1999=true := by decide +kernel
theorem fusedMap1999_checked : acceptsGraphIso
    (fused (graph core1999) (root 10) 0 0) DegreeOneSmallSpectrum1424.graph fusedMap1999=true := by decide +kernel
theorem certified1999 : Certified (graph core1999) (root 10) 0 0 :=
  of_native_maps core1999 DegreeOneSmallSpectrum1236.graph DegreeOneSmallSpectrum1424.graph
    sourceMap1999 fusedMap1999 sourceMap1999_checked fusedMap1999_checked
    DegreeOneSmallComparisons.comparison1999
#print axioms sourceMap1999_checked
#print axioms fusedMap1999_checked
#print axioms certified1999
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
