/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1810 : Family 10 := level10.get ⟨53,by decide⟩
def sourceMap1810 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1810 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1810_checked : acceptsGraphIso
    (source (graph core1810) (root 10) 0 0) DegreeOneSmallSpectrum1001.graph sourceMap1810=true := by decide +kernel
theorem fusedMap1810_checked : acceptsGraphIso
    (fused (graph core1810) (root 10) 0 0) DegreeOneSmallSpectrum862.graph fusedMap1810=true := by decide +kernel
theorem certified1810 : Certified (graph core1810) (root 10) 0 0 :=
  of_native_maps core1810 DegreeOneSmallSpectrum1001.graph DegreeOneSmallSpectrum862.graph
    sourceMap1810 fusedMap1810 sourceMap1810_checked fusedMap1810_checked
    DegreeOneSmallComparisons.comparison1810
#print axioms sourceMap1810_checked
#print axioms fusedMap1810_checked
#print axioms certified1810
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
