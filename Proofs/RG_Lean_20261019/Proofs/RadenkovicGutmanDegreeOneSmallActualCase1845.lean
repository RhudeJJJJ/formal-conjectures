/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1845 : Family 10 := level10.get ⟨97,by decide⟩
def sourceMap1845 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1845 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1845_checked : acceptsGraphIso
    (source (graph core1845) (root 10) 0 0) DegreeOneSmallSpectrum1169.graph sourceMap1845=true := by decide +kernel
theorem fusedMap1845_checked : acceptsGraphIso
    (fused (graph core1845) (root 10) 0 0) DegreeOneSmallSpectrum920.graph fusedMap1845=true := by decide +kernel
theorem certified1845 : Certified (graph core1845) (root 10) 0 0 :=
  of_native_maps core1845 DegreeOneSmallSpectrum1169.graph DegreeOneSmallSpectrum920.graph
    sourceMap1845 fusedMap1845 sourceMap1845_checked fusedMap1845_checked
    DegreeOneSmallComparisons.comparison1845
#print axioms sourceMap1845_checked
#print axioms fusedMap1845_checked
#print axioms certified1845
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
