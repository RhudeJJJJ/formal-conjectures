/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1213 : Family 9 := level9.get ⟨10,by decide⟩
def sourceMap1213 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1213 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1213_checked : acceptsGraphIso
    (source (graph core1213) (root 9) 0 0) DegreeOneSmallSpectrum449.graph sourceMap1213=true := by decide +kernel
theorem fusedMap1213_checked : acceptsGraphIso
    (fused (graph core1213) (root 9) 0 0) DegreeOneSmallSpectrum371.graph fusedMap1213=true := by decide +kernel
theorem certified1213 : Certified (graph core1213) (root 9) 0 0 :=
  of_native_maps core1213 DegreeOneSmallSpectrum449.graph DegreeOneSmallSpectrum371.graph
    sourceMap1213 fusedMap1213 sourceMap1213_checked fusedMap1213_checked
    DegreeOneSmallComparisons.comparison1213
#print axioms sourceMap1213_checked
#print axioms fusedMap1213_checked
#print axioms certified1213
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
