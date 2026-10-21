/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1126 : Family 8 := level8.get ⟨166,by decide⟩
def sourceMap1126 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap1126 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1126_checked : acceptsGraphIso
    (source (graph core1126) (root 8) 1 1) DegreeOneSmallSpectrum1929.graph sourceMap1126=true := by decide +kernel
theorem fusedMap1126_checked : acceptsGraphIso
    (fused (graph core1126) (root 8) 1 1) DegreeOneSmallSpectrum1478.graph fusedMap1126=true := by decide +kernel
theorem certified1126 : Certified (graph core1126) (root 8) 1 1 :=
  of_native_maps core1126 DegreeOneSmallSpectrum1929.graph DegreeOneSmallSpectrum1478.graph
    sourceMap1126 fusedMap1126 sourceMap1126_checked fusedMap1126_checked
    DegreeOneSmallComparisons.comparison1126
#print axioms sourceMap1126_checked
#print axioms fusedMap1126_checked
#print axioms certified1126
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
