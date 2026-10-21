/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1239 : Family 9 := level9.get ⟨25,by decide⟩
def sourceMap1239 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1239 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1239_checked : acceptsGraphIso
    (source (graph core1239) (root 9) 0 0) DegreeOneSmallSpectrum497.graph sourceMap1239=true := by decide +kernel
theorem fusedMap1239_checked : acceptsGraphIso
    (fused (graph core1239) (root 9) 0 0) DegreeOneSmallSpectrum389.graph fusedMap1239=true := by decide +kernel
theorem certified1239 : Certified (graph core1239) (root 9) 0 0 :=
  of_native_maps core1239 DegreeOneSmallSpectrum497.graph DegreeOneSmallSpectrum389.graph
    sourceMap1239 fusedMap1239 sourceMap1239_checked fusedMap1239_checked
    DegreeOneSmallComparisons.comparison1239
#print axioms sourceMap1239_checked
#print axioms fusedMap1239_checked
#print axioms certified1239
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
