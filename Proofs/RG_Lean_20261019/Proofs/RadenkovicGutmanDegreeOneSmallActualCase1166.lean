/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1166 : Family 8 := level8.get ⟨207,by decide⟩
def sourceMap1166 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1166 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1166_checked : acceptsGraphIso
    (source (graph core1166) (root 8) 1 1) DegreeOneSmallSpectrum1708.graph sourceMap1166=true := by decide +kernel
theorem fusedMap1166_checked : acceptsGraphIso
    (fused (graph core1166) (root 8) 1 1) DegreeOneSmallSpectrum1083.graph fusedMap1166=true := by decide +kernel
theorem certified1166 : Certified (graph core1166) (root 8) 1 1 :=
  of_native_maps core1166 DegreeOneSmallSpectrum1708.graph DegreeOneSmallSpectrum1083.graph
    sourceMap1166 fusedMap1166 sourceMap1166_checked fusedMap1166_checked
    DegreeOneSmallComparisons.comparison1166
#print axioms sourceMap1166_checked
#print axioms fusedMap1166_checked
#print axioms certified1166
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
