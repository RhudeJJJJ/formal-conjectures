/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1303 : Family 9 := level9.get ⟨70,by decide⟩
def sourceMap1303 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1303 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1303_checked : acceptsGraphIso
    (source (graph core1303) (root 9) 0 0) DegreeOneSmallSpectrum482.graph sourceMap1303=true := by decide +kernel
theorem fusedMap1303_checked : acceptsGraphIso
    (fused (graph core1303) (root 9) 0 0) DegreeOneSmallSpectrum510.graph fusedMap1303=true := by decide +kernel
theorem certified1303 : Certified (graph core1303) (root 9) 0 0 :=
  of_native_maps core1303 DegreeOneSmallSpectrum482.graph DegreeOneSmallSpectrum510.graph
    sourceMap1303 fusedMap1303 sourceMap1303_checked fusedMap1303_checked
    DegreeOneSmallComparisons.comparison1303
#print axioms sourceMap1303_checked
#print axioms fusedMap1303_checked
#print axioms certified1303
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
