/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1179 : Family 8 := level8.get ⟨230,by decide⟩
def sourceMap1179 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1179 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1179_checked : acceptsGraphIso
    (source (graph core1179) (root 8) 0 0) SmallGeFourSpectrum085.graph sourceMap1179=true := by decide +kernel
theorem fusedMap1179_checked : acceptsGraphIso
    (fused (graph core1179) (root 8) 0 0) SmallGeFourSpectrum055.graph fusedMap1179=true := by decide +kernel
theorem certified1179 : Certified (graph core1179) (root 8) 0 0 :=
  of_native_maps core1179 SmallGeFourSpectrum085.graph SmallGeFourSpectrum055.graph
    sourceMap1179 fusedMap1179 sourceMap1179_checked fusedMap1179_checked
    DegreeOneSmallComparisons.comparison1179
#print axioms sourceMap1179_checked
#print axioms fusedMap1179_checked
#print axioms certified1179
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
