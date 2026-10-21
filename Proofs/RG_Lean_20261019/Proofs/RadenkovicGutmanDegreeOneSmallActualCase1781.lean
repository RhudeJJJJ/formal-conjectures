/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1781 : Family 10 := level10.get ⟨15,by decide⟩
def sourceMap1781 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1781 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1781_checked : acceptsGraphIso
    (source (graph core1781) (root 10) 0 0) DegreeOneSmallSpectrum883.graph sourceMap1781=true := by decide +kernel
theorem fusedMap1781_checked : acceptsGraphIso
    (fused (graph core1781) (root 10) 0 0) DegreeOneSmallSpectrum907.graph fusedMap1781=true := by decide +kernel
theorem certified1781 : Certified (graph core1781) (root 10) 0 0 :=
  of_native_maps core1781 DegreeOneSmallSpectrum883.graph DegreeOneSmallSpectrum907.graph
    sourceMap1781 fusedMap1781 sourceMap1781_checked fusedMap1781_checked
    DegreeOneSmallComparisons.comparison1781
#print axioms sourceMap1781_checked
#print axioms fusedMap1781_checked
#print axioms certified1781
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
