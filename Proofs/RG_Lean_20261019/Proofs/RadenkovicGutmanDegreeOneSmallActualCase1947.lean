/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1947 : Family 10 := level10.get ⟨247,by decide⟩
def sourceMap1947 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1947 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1947_checked : acceptsGraphIso
    (source (graph core1947) (root 10) 0 0) DegreeOneSmallSpectrum1217.graph sourceMap1947=true := by decide +kernel
theorem fusedMap1947_checked : acceptsGraphIso
    (fused (graph core1947) (root 10) 0 0) DegreeOneSmallSpectrum1226.graph fusedMap1947=true := by decide +kernel
theorem certified1947 : Certified (graph core1947) (root 10) 0 0 :=
  of_native_maps core1947 DegreeOneSmallSpectrum1217.graph DegreeOneSmallSpectrum1226.graph
    sourceMap1947 fusedMap1947 sourceMap1947_checked fusedMap1947_checked
    DegreeOneSmallComparisons.comparison1947
#print axioms sourceMap1947_checked
#print axioms fusedMap1947_checked
#print axioms certified1947
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
