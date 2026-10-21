/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1794 : Family 10 := level10.get ⟨30,by decide⟩
def sourceMap1794 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1794 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1794_checked : acceptsGraphIso
    (source (graph core1794) (root 10) 0 0) DegreeOneSmallSpectrum885.graph sourceMap1794=true := by decide +kernel
theorem fusedMap1794_checked : acceptsGraphIso
    (fused (graph core1794) (root 10) 0 0) DegreeOneSmallSpectrum965.graph fusedMap1794=true := by decide +kernel
theorem certified1794 : Certified (graph core1794) (root 10) 0 0 :=
  of_native_maps core1794 DegreeOneSmallSpectrum885.graph DegreeOneSmallSpectrum965.graph
    sourceMap1794 fusedMap1794 sourceMap1794_checked fusedMap1794_checked
    DegreeOneSmallComparisons.comparison1794
#print axioms sourceMap1794_checked
#print axioms fusedMap1794_checked
#print axioms certified1794
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
