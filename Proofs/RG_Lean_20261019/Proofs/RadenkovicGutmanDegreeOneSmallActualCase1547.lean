/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1547 : Family 9 := level9.get ⟨276,by decide⟩
def sourceMap1547 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1547 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1547_checked : acceptsGraphIso
    (source (graph core1547) (root 9) 0 0) DegreeOneSmallSpectrum683.graph sourceMap1547=true := by decide +kernel
theorem fusedMap1547_checked : acceptsGraphIso
    (fused (graph core1547) (root 9) 0 0) DegreeOneSmallSpectrum566.graph fusedMap1547=true := by decide +kernel
theorem certified1547 : Certified (graph core1547) (root 9) 0 0 :=
  of_native_maps core1547 DegreeOneSmallSpectrum683.graph DegreeOneSmallSpectrum566.graph
    sourceMap1547 fusedMap1547 sourceMap1547_checked fusedMap1547_checked
    DegreeOneSmallComparisons.comparison1547
#print axioms sourceMap1547_checked
#print axioms fusedMap1547_checked
#print axioms certified1547
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
