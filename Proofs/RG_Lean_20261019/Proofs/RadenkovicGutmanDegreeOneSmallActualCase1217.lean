/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1217 : Family 9 := level9.get ⟨12,by decide⟩
def sourceMap1217 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1217 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1217_checked : acceptsGraphIso
    (source (graph core1217) (root 9) 0 0) DegreeOneSmallSpectrum480.graph sourceMap1217=true := by decide +kernel
theorem fusedMap1217_checked : acceptsGraphIso
    (fused (graph core1217) (root 9) 0 0) DegreeOneSmallSpectrum373.graph fusedMap1217=true := by decide +kernel
theorem certified1217 : Certified (graph core1217) (root 9) 0 0 :=
  of_native_maps core1217 DegreeOneSmallSpectrum480.graph DegreeOneSmallSpectrum373.graph
    sourceMap1217 fusedMap1217 sourceMap1217_checked fusedMap1217_checked
    DegreeOneSmallComparisons.comparison1217
#print axioms sourceMap1217_checked
#print axioms fusedMap1217_checked
#print axioms certified1217
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
