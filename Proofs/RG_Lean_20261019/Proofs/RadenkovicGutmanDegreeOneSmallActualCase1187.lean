/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1187 : Family 8 := level8.get ⟨240,by decide⟩
def sourceMap1187 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1187 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1187_checked : acceptsGraphIso
    (source (graph core1187) (root 8) 0 0) SmallGeFourSpectrum087.graph sourceMap1187=true := by decide +kernel
theorem fusedMap1187_checked : acceptsGraphIso
    (fused (graph core1187) (root 8) 0 0) SmallGeFourSpectrum060.graph fusedMap1187=true := by decide +kernel
theorem certified1187 : Certified (graph core1187) (root 8) 0 0 :=
  of_native_maps core1187 SmallGeFourSpectrum087.graph SmallGeFourSpectrum060.graph
    sourceMap1187 fusedMap1187 sourceMap1187_checked fusedMap1187_checked
    DegreeOneSmallComparisons.comparison1187
#print axioms sourceMap1187_checked
#print axioms fusedMap1187_checked
#print axioms certified1187
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
