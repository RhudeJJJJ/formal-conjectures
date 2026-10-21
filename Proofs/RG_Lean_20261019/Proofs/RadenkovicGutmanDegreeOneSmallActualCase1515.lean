/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1515 : Family 9 := level9.get ⟨243,by decide⟩
def sourceMap1515 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1515 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1515_checked : acceptsGraphIso
    (source (graph core1515) (root 9) 0 0) DegreeOneSmallSpectrum717.graph sourceMap1515=true := by decide +kernel
theorem fusedMap1515_checked : acceptsGraphIso
    (fused (graph core1515) (root 9) 0 0) SmallGeFourSpectrum106.graph fusedMap1515=true := by decide +kernel
theorem certified1515 : Certified (graph core1515) (root 9) 0 0 :=
  of_native_maps core1515 DegreeOneSmallSpectrum717.graph SmallGeFourSpectrum106.graph
    sourceMap1515 fusedMap1515 sourceMap1515_checked fusedMap1515_checked
    DegreeOneSmallComparisons.comparison1515
#print axioms sourceMap1515_checked
#print axioms fusedMap1515_checked
#print axioms certified1515
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
