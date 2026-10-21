/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1641 : Family 9 := level9.get ⟨387,by decide⟩
def sourceMap1641 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1641 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1641_checked : acceptsGraphIso
    (source (graph core1641) (root 9) 0 0) DegreeOneSmallSpectrum762.graph sourceMap1641=true := by decide +kernel
theorem fusedMap1641_checked : acceptsGraphIso
    (fused (graph core1641) (root 9) 0 0) DegreeOneSmallSpectrum761.graph fusedMap1641=true := by decide +kernel
theorem certified1641 : Certified (graph core1641) (root 9) 0 0 :=
  of_native_maps core1641 DegreeOneSmallSpectrum762.graph DegreeOneSmallSpectrum761.graph
    sourceMap1641 fusedMap1641 sourceMap1641_checked fusedMap1641_checked
    DegreeOneSmallComparisons.comparison1641
#print axioms sourceMap1641_checked
#print axioms fusedMap1641_checked
#print axioms certified1641
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
