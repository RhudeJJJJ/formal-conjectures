/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1083 : Family 8 := level8.get ⟨142,by decide⟩
def sourceMap1083 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (sourceLabel 8 0 0 v)
def fusedMap1083 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap1083_checked : acceptsGraphIso
    (source (graph core1083) (root 8) 0 0) SmallGeFourSpectrum050.graph sourceMap1083=true := by decide +kernel
theorem fusedMap1083_checked : acceptsGraphIso
    (fused (graph core1083) (root 8) 0 0) SmallGeFourSpectrum065.graph fusedMap1083=true := by decide +kernel
theorem certified1083 : Certified (graph core1083) (root 8) 0 0 :=
  of_native_maps core1083 SmallGeFourSpectrum050.graph SmallGeFourSpectrum065.graph
    sourceMap1083 fusedMap1083 sourceMap1083_checked fusedMap1083_checked
    DegreeOneSmallComparisons.comparison1083
#print axioms sourceMap1083_checked
#print axioms fusedMap1083_checked
#print axioms certified1083
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
