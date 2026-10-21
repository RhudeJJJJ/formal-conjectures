/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1267 : Family 9 := level9.get ⟨45,by decide⟩
def sourceMap1267 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1267 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1267_checked : acceptsGraphIso
    (source (graph core1267) (root 9) 0 0) DegreeOneSmallSpectrum414.graph sourceMap1267=true := by decide +kernel
theorem fusedMap1267_checked : acceptsGraphIso
    (fused (graph core1267) (root 9) 0 0) DegreeOneSmallSpectrum417.graph fusedMap1267=true := by decide +kernel
theorem certified1267 : Certified (graph core1267) (root 9) 0 0 :=
  of_native_maps core1267 DegreeOneSmallSpectrum414.graph DegreeOneSmallSpectrum417.graph
    sourceMap1267 fusedMap1267 sourceMap1267_checked fusedMap1267_checked
    DegreeOneSmallComparisons.comparison1267
#print axioms sourceMap1267_checked
#print axioms fusedMap1267_checked
#print axioms certified1267
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
