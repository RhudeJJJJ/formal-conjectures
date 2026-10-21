/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1223 : Family 9 := level9.get ⟨16,by decide⟩
def sourceMap1223 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,4,5] (sourceLabel 9 0 0 v)
def fusedMap1223 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1223_checked : acceptsGraphIso
    (source (graph core1223) (root 9) 0 0) DegreeOneSmallSpectrum483.graph sourceMap1223=true := by decide +kernel
theorem fusedMap1223_checked : acceptsGraphIso
    (fused (graph core1223) (root 9) 0 0) DegreeOneSmallSpectrum379.graph fusedMap1223=true := by decide +kernel
theorem certified1223 : Certified (graph core1223) (root 9) 0 0 :=
  of_native_maps core1223 DegreeOneSmallSpectrum483.graph DegreeOneSmallSpectrum379.graph
    sourceMap1223 fusedMap1223 sourceMap1223_checked fusedMap1223_checked
    DegreeOneSmallComparisons.comparison1223
#print axioms sourceMap1223_checked
#print axioms fusedMap1223_checked
#print axioms certified1223
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
