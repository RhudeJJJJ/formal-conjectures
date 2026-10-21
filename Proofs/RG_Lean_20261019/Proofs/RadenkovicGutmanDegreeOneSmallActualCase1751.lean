/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1751 : Family 9 := level9.get ⟨590,by decide⟩
def sourceMap1751 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1751 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1751_checked : acceptsGraphIso
    (source (graph core1751) (root 9) 0 0) SmallGeFourSpectrum222.graph sourceMap1751=true := by decide +kernel
theorem fusedMap1751_checked : acceptsGraphIso
    (fused (graph core1751) (root 9) 0 0) SmallGeFourSpectrum140.graph fusedMap1751=true := by decide +kernel
theorem certified1751 : Certified (graph core1751) (root 9) 0 0 :=
  of_native_maps core1751 SmallGeFourSpectrum222.graph SmallGeFourSpectrum140.graph
    sourceMap1751 fusedMap1751 sourceMap1751_checked fusedMap1751_checked
    DegreeOneSmallComparisons.comparison1751
#print axioms sourceMap1751_checked
#print axioms fusedMap1751_checked
#print axioms certified1751
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
