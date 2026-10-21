/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1823 : Family 10 := level10.get ⟨68,by decide⟩
def sourceMap1823 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1823 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1823_checked : acceptsGraphIso
    (source (graph core1823) (root 10) 0 0) DegreeOneSmallSpectrum1218.graph sourceMap1823=true := by decide +kernel
theorem fusedMap1823_checked : acceptsGraphIso
    (fused (graph core1823) (root 10) 0 0) DegreeOneSmallSpectrum881.graph fusedMap1823=true := by decide +kernel
theorem certified1823 : Certified (graph core1823) (root 10) 0 0 :=
  of_native_maps core1823 DegreeOneSmallSpectrum1218.graph DegreeOneSmallSpectrum881.graph
    sourceMap1823 fusedMap1823 sourceMap1823_checked fusedMap1823_checked
    DegreeOneSmallComparisons.comparison1823
#print axioms sourceMap1823_checked
#print axioms fusedMap1823_checked
#print axioms certified1823
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
