/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1035 : Family 8 := level8.get ⟨115,by decide⟩
def sourceMap1035 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (sourceLabel 8 0 0 v)
def fusedMap1035 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap1035_checked : acceptsGraphIso
    (source (graph core1035) (root 8) 0 0) DegreeOneSmallSpectrum276.graph sourceMap1035=true := by decide +kernel
theorem fusedMap1035_checked : acceptsGraphIso
    (fused (graph core1035) (root 8) 0 0) DegreeOneSmallSpectrum299.graph fusedMap1035=true := by decide +kernel
theorem certified1035 : Certified (graph core1035) (root 8) 0 0 :=
  of_native_maps core1035 DegreeOneSmallSpectrum276.graph DegreeOneSmallSpectrum299.graph
    sourceMap1035 fusedMap1035 sourceMap1035_checked fusedMap1035_checked
    DegreeOneSmallComparisons.comparison1035
#print axioms sourceMap1035_checked
#print axioms fusedMap1035_checked
#print axioms certified1035
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
