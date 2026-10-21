/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1969 : Family 10 := level10.get ⟨287,by decide⟩
def sourceMap1969 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1969 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1969_checked : acceptsGraphIso
    (source (graph core1969) (root 10) 0 0) DegreeOneSmallSpectrum1229.graph sourceMap1969=true := by decide +kernel
theorem fusedMap1969_checked : acceptsGraphIso
    (fused (graph core1969) (root 10) 0 0) DegreeOneSmallSpectrum1313.graph fusedMap1969=true := by decide +kernel
theorem certified1969 : Certified (graph core1969) (root 10) 0 0 :=
  of_native_maps core1969 DegreeOneSmallSpectrum1229.graph DegreeOneSmallSpectrum1313.graph
    sourceMap1969 fusedMap1969 sourceMap1969_checked fusedMap1969_checked
    DegreeOneSmallComparisons.comparison1969
#print axioms sourceMap1969_checked
#print axioms fusedMap1969_checked
#print axioms certified1969
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
