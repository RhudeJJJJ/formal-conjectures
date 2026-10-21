/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1741 : Family 9 := level9.get ⟨564,by decide⟩
def sourceMap1741 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 9 0 0 v)
def fusedMap1741 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1741_checked : acceptsGraphIso
    (source (graph core1741) (root 9) 0 0) DegreeOneSmallSpectrum844.graph sourceMap1741=true := by decide +kernel
theorem fusedMap1741_checked : acceptsGraphIso
    (fused (graph core1741) (root 9) 0 0) DegreeOneSmallSpectrum631.graph fusedMap1741=true := by decide +kernel
theorem certified1741 : Certified (graph core1741) (root 9) 0 0 :=
  of_native_maps core1741 DegreeOneSmallSpectrum844.graph DegreeOneSmallSpectrum631.graph
    sourceMap1741 fusedMap1741 sourceMap1741_checked fusedMap1741_checked
    DegreeOneSmallComparisons.comparison1741
#print axioms sourceMap1741_checked
#print axioms fusedMap1741_checked
#print axioms certified1741
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
