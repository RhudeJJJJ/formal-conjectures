/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1237 : Family 9 := level9.get ⟨24,by decide⟩
def sourceMap1237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1237 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1237_checked : acceptsGraphIso
    (source (graph core1237) (root 9) 0 0) DegreeOneSmallSpectrum496.graph sourceMap1237=true := by decide +kernel
theorem fusedMap1237_checked : acceptsGraphIso
    (fused (graph core1237) (root 9) 0 0) DegreeOneSmallSpectrum388.graph fusedMap1237=true := by decide +kernel
theorem certified1237 : Certified (graph core1237) (root 9) 0 0 :=
  of_native_maps core1237 DegreeOneSmallSpectrum496.graph DegreeOneSmallSpectrum388.graph
    sourceMap1237 fusedMap1237 sourceMap1237_checked fusedMap1237_checked
    DegreeOneSmallComparisons.comparison1237
#print axioms sourceMap1237_checked
#print axioms fusedMap1237_checked
#print axioms certified1237
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
